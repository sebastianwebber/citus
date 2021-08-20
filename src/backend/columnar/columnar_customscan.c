/*-------------------------------------------------------------------------
 *
 * columnar_customscan.c
 *
 * This file contains the implementation of a postgres custom scan that
 * we use to push down the projections into the table access methods.
 *
 * $Id$
 *
 *-------------------------------------------------------------------------
 */

#include "citus_version.h"

#include "postgres.h"

#include <math.h>

#include "access/amapi.h"
#include "access/skey.h"
#include "catalog/pg_am.h"
#include "catalog/pg_statistic.h"
#include "commands/defrem.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pg_list.h"
#include "nodes/plannodes.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/restrictinfo.h"
#include "utils/lsyscache.h"
#include "utils/relcache.h"
#include "utils/ruleutils.h"
#include "utils/selfuncs.h"
#include "utils/spccache.h"

#include "columnar/columnar.h"
#include "columnar/columnar_customscan.h"
#include "columnar/columnar_metadata.h"
#include "columnar/columnar_tableam.h"
#include "distributed/listutils.h"

/*
 * ColumnarScanState represents the state for a columnar scan. It's a
 * CustomScanState with additional fields specific to columnar scans.
 */
typedef struct ColumnarScanState
{
	CustomScanState custom_scanstate; /* must be first field */

	ExprContext *css_RuntimeContext;
	List *qual;
} ColumnarScanState;


typedef bool (*PathPredicate)(Path *path);


static void ColumnarSetRelPathlistHook(PlannerInfo *root, RelOptInfo *rel, Index rti,
									   RangeTblEntry *rte);
static void RemovePathsByPredicate(RelOptInfo *rel, PathPredicate removePathPredicate);
static bool IsNotIndexPath(Path *path);
static Path * CreateColumnarSeqScanPath(PlannerInfo *root, RelOptInfo *rel,
										Oid relationId);
static void RecostColumnarPaths(PlannerInfo *root, RelOptInfo *rel, Oid relationId);
static void RecostColumnarIndexPath(PlannerInfo *root, RelOptInfo *rel, Oid relationId,
									IndexPath *indexPath);
static Cost ColumnarIndexScanAddStartupCost(RelOptInfo *rel, Oid relationId,
											IndexPath *indexPath);
static Cost ColumnarIndexScanAddTotalCost(PlannerInfo *root, RelOptInfo *rel,
										  Oid relationId, IndexPath *indexPath);
static void CostColumnarSeqPath(RelOptInfo *rel, Oid relationId, Path *path);
static int RelationIdGetNumberOfAttributes(Oid relationId);
static void AddColumnarScanPaths(PlannerInfo *root, RelOptInfo *rel,
								 RangeTblEntry *rte);
static void AddColumnarScanPathsRec(PlannerInfo *root, RelOptInfo *rel,
									RangeTblEntry *rte, Relids paramRelids,
									Relids candidateRelids,
									int depthLimit);
static void AddColumnarScanPath(PlannerInfo *root, RelOptInfo *rel,
								RangeTblEntry *rte, Relids required_relids);
static void CostColumnarScan(CustomPath *cpath, PlannerInfo *root,
							 RelOptInfo *rel, Oid relationId,
							 int numberOfColumnsRead, int nClauses);
static Cost ColumnarPerStripeScanCost(RelOptInfo *rel, Oid relationId,
									  int numberOfColumnsRead);
static uint64 ColumnarTableStripeCount(Oid relationId);
static Plan * ColumnarScanPath_PlanCustomPath(PlannerInfo *root,
											  RelOptInfo *rel,
											  struct CustomPath *best_path,
											  List *tlist,
											  List *clauses,
											  List *custom_plans);

static Node * ColumnarScan_CreateCustomScanState(CustomScan *cscan);

static void ColumnarScan_BeginCustomScan(CustomScanState *node, EState *estate, int
										 eflags);
static TupleTableSlot * ColumnarScan_ExecCustomScan(CustomScanState *node);
static void ColumnarScan_EndCustomScan(CustomScanState *node);
static void ColumnarScan_ReScanCustomScan(CustomScanState *node);
static void ColumnarScan_ExplainCustomScan(CustomScanState *node, List *ancestors,
										   ExplainState *es);

/* saved hook value in case of unload */
static set_rel_pathlist_hook_type PreviousSetRelPathlistHook = NULL;

static bool EnableColumnarCustomScan = true;
static bool EnableColumnarQualPushdown = true;
static double ColumnarQualPushdownCorrelation = 0.9;
static int ColumnarMaxCustomScanPaths = 64;


const struct CustomPathMethods ColumnarScanPathMethods = {
	.CustomName = "ColumnarScan",
	.PlanCustomPath = ColumnarScanPath_PlanCustomPath,
};

const struct CustomScanMethods ColumnarScanScanMethods = {
	.CustomName = "ColumnarScan",
	.CreateCustomScanState = ColumnarScan_CreateCustomScanState,
};

const struct CustomExecMethods ColumnarScanExecuteMethods = {
	.CustomName = "ColumnarScan",

	.BeginCustomScan = ColumnarScan_BeginCustomScan,
	.ExecCustomScan = ColumnarScan_ExecCustomScan,
	.EndCustomScan = ColumnarScan_EndCustomScan,
	.ReScanCustomScan = ColumnarScan_ReScanCustomScan,

	.ExplainCustomScan = ColumnarScan_ExplainCustomScan,
};


/*
 * columnar_customscan_init installs the hook required to intercept the postgres planner and
 * provide extra paths for columnar tables
 */
void
columnar_customscan_init()
{
	PreviousSetRelPathlistHook = set_rel_pathlist_hook;
	set_rel_pathlist_hook = ColumnarSetRelPathlistHook;

	/* register customscan specific GUC's */
	DefineCustomBoolVariable(
		"columnar.enable_custom_scan",
		gettext_noop("Enables the use of a custom scan to push projections and quals "
					 "into the storage layer."),
		NULL,
		&EnableColumnarCustomScan,
		true,
		PGC_USERSET,
		GUC_NO_SHOW_ALL,
		NULL, NULL, NULL);
	DefineCustomBoolVariable(
		"columnar.enable_qual_pushdown",
		gettext_noop("Enables qual pushdown into columnar. This has no effect unless "
					 "columnar.enable_custom_scan is true."),
		NULL,
		&EnableColumnarQualPushdown,
		true,
		PGC_USERSET,
		GUC_NO_SHOW_ALL,
		NULL, NULL, NULL);
	DefineCustomRealVariable(
		"columnar.qual_pushdown_correlation",
		gettext_noop("Correlation threshold to attempt to push a qual "
					 "referencing the given column. A value of 0 means "
					 "attempt to push down all quals, even if the column "
					 "is uncorrelated."),
		NULL,
		&ColumnarQualPushdownCorrelation,
		0.9,
		0.0,
		1.0,
		PGC_USERSET,
		GUC_NO_SHOW_ALL,
		NULL, NULL, NULL);
	DefineCustomIntVariable(
		"columnar.max_custom_scan_paths",
		gettext_noop("Maximum number of custom scan paths to generate "
					 "for a columnar table when planning."),
		NULL,
		&ColumnarMaxCustomScanPaths,
		64,
		1,
		1024,
		PGC_USERSET,
		GUC_NO_SHOW_ALL,
		NULL, NULL, NULL);

	RegisterCustomScanMethods(&ColumnarScanScanMethods);
}


static void
ColumnarSetRelPathlistHook(PlannerInfo *root, RelOptInfo *rel, Index rti,
						   RangeTblEntry *rte)
{
	/* call into previous hook if assigned */
	if (PreviousSetRelPathlistHook)
	{
		PreviousSetRelPathlistHook(root, rel, rti, rte);
	}

	if (!OidIsValid(rte->relid) || rte->rtekind != RTE_RELATION || rte->inh)
	{
		/* some calls to the pathlist hook don't have a valid relation set. Do nothing */
		return;
	}

	/*
	 * Here we want to inspect if this relation pathlist hook is accessing a columnar table.
	 * If that is the case we want to insert an extra path that pushes down the projection
	 * into the scan of the table to minimize the data read.
	 */
	Relation relation = RelationIdGetRelation(rte->relid);
	if (relation->rd_tableam == GetColumnarTableAmRoutine())
	{
		if (rte->tablesample != NULL)
		{
			ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							errmsg("sample scans not supported on columnar tables")));
		}

		/* columnar doesn't support parallel paths */
		rel->partial_pathlist = NIL;

		/*
		 * There are cases where IndexPath is normally more preferrable over
		 * SeqPath for heapAM but not for columnarAM. In such cases, an
		 * IndexPath could wrongly dominate a SeqPath based on the costs
		 * estimated by postgres earlier. For this reason, here we manually
		 * create a SeqPath, estimate the cost based on columnarAM and append
		 * to pathlist.
		 *
		 * Before doing that, we first re-cost all the existing paths so that
		 * add_path makes correct cost comparisons when appending our SeqPath.
		 */
		RecostColumnarPaths(root, rel, rte->relid);

		Path *seqPath = CreateColumnarSeqScanPath(root, rel, rte->relid);
		add_path(rel, seqPath);

		if (EnableColumnarCustomScan)
		{
			ereport(DEBUG1, (errmsg("pathlist hook for columnar table am")));

			/*
			 * When columnar custom scan is enabled (columnar.enable_custom_scan),
			 * we only consider ColumnarScanPath's & IndexPath's. For this reason,
			 * we remove other paths and re-estimate IndexPath costs to make accurate
			 * comparisons between them.
			 *
			 * Even more, we might calculate an equal cost for a
			 * ColumnarCustomScan and a SeqPath if we are reading all columns
			 * of given table since we don't consider chunk group filtering
			 * when costing ColumnarCustomScan.
			 * In that case, if we don't remove SeqPath's, we might wrongly choose
			 * SeqPath thinking that its cost would be equal to ColumnarCustomScan.
			 */
			RemovePathsByPredicate(rel, IsNotIndexPath);
			AddColumnarScanPaths(root, rel, rte);
		}
	}
	RelationClose(relation);
}


/*
 * RemovePathsByPredicate removes the paths that removePathPredicate
 * evaluates to true from pathlist of given rel.
 */
static void
RemovePathsByPredicate(RelOptInfo *rel, PathPredicate removePathPredicate)
{
	List *filteredPathList = NIL;

	Path *path = NULL;
	foreach_ptr(path, rel->pathlist)
	{
		if (!removePathPredicate(path))
		{
			filteredPathList = lappend(filteredPathList, path);
		}
	}

	rel->pathlist = filteredPathList;
}


/*
 * IsNotIndexPath returns true if given path is not an IndexPath.
 */
static bool
IsNotIndexPath(Path *path)
{
	return !IsA(path, IndexPath);
}


/*
 * CreateColumnarSeqScanPath returns Path for sequential scan on columnar
 * table with relationId.
 */
static Path *
CreateColumnarSeqScanPath(PlannerInfo *root, RelOptInfo *rel, Oid relationId)
{
	/* columnar doesn't support parallel scan */
	int parallelWorkers = 0;

	Relids requiredOuter = rel->lateral_relids;
	Path *path = create_seqscan_path(root, rel, requiredOuter, parallelWorkers);
	CostColumnarSeqPath(rel, relationId, path);
	return path;
}


/*
 * RecostColumnarPaths re-costs paths of given RelOptInfo for
 * columnar table with relationId.
 */
static void
RecostColumnarPaths(PlannerInfo *root, RelOptInfo *rel, Oid relationId)
{
	Path *path = NULL;
	foreach_ptr(path, rel->pathlist)
	{
		if (IsA(path, IndexPath))
		{
			/*
			 * Since we don't provide implementations for scan_bitmap_next_block
			 * & scan_bitmap_next_tuple, postgres doesn't generate bitmap index
			 * scan paths for columnar tables already (see related comments in
			 * TableAmRoutine). For this reason, we only consider IndexPath's
			 * here.
			 */
			RecostColumnarIndexPath(root, rel, relationId, (IndexPath *) path);
		}
		else if (path->pathtype == T_SeqScan)
		{
			CostColumnarSeqPath(rel, relationId, path);
		}
	}
}


/*
 * RecostColumnarIndexPath re-costs given index path for columnar table with
 * relationId.
 */
static void
RecostColumnarIndexPath(PlannerInfo *root, RelOptInfo *rel, Oid relationId,
						IndexPath *indexPath)
{
	if (!enable_indexscan)
	{
		/* costs are already set to disable_cost, don't adjust them */
		return;
	}

	ereport(DEBUG4, (errmsg("columnar table index scan costs estimated by "
							"indexAM: startup cost = %.10f, total cost = "
							"%.10f", indexPath->path.startup_cost,
							indexPath->path.total_cost)));

	/*
	 * We estimate the cost for columnar table read during index scan. Also,
	 * instead of overwriting startup & total costs, we "add" ours to the
	 * costs estimated by indexAM since we should consider index traversal
	 * related costs too.
	 */
	Cost indexAMStartupCost = indexPath->path.startup_cost;
	Cost indexAMScanCost = indexPath->path.total_cost - indexAMStartupCost;

	Cost columnarIndexScanStartupCost = ColumnarIndexScanAddStartupCost(rel, relationId,
																		indexPath);
	Cost columnarIndexScanCost = ColumnarIndexScanAddTotalCost(root, rel, relationId,
															   indexPath);

	indexPath->path.startup_cost = indexAMStartupCost + columnarIndexScanStartupCost;
	indexPath->path.total_cost = indexPath->path.startup_cost +
								 indexAMScanCost + columnarIndexScanCost;

	ereport(DEBUG4, (errmsg("columnar table index scan costs re-estimated "
							"by columnarAM (including indexAM costs): "
							"startup cost = %.10f, total cost = %.10f",
							indexPath->path.startup_cost,
							indexPath->path.total_cost)));
}


/*
 * ColumnarIndexScanAddStartupCost returns additional startup cost estimated
 * for index scan described by IndexPath for columnar table with relationId.
 */
static Cost
ColumnarIndexScanAddStartupCost(RelOptInfo *rel, Oid relationId, IndexPath *indexPath)
{
	int numberOfColumnsRead = RelationIdGetNumberOfAttributes(relationId);

	/* we would at least read one stripe */
	return ColumnarPerStripeScanCost(rel, relationId, numberOfColumnsRead);
}


/*
 * ColumnarIndexScanAddTotalCost returns additional cost estimated for
 * index scan described by IndexPath for columnar table with relationId.
 */
static Cost
ColumnarIndexScanAddTotalCost(PlannerInfo *root, RelOptInfo *rel,
							  Oid relationId, IndexPath *indexPath)
{
	int numberOfColumnsRead = RelationIdGetNumberOfAttributes(relationId);
	Cost perStripeCost = ColumnarPerStripeScanCost(rel, relationId, numberOfColumnsRead);

	/*
	 * We don't need to pass correct loop count to amcostestimate since we
	 * will only use index correlation & index selectivity, and loop count
	 * doesn't have any effect on those two.
	 */
	double fakeLoopCount = 1;
	Cost fakeIndexStartupCost;
	Cost fakeIndexTotalCost;
	double fakeIndexPages;
	Selectivity indexSelectivity;
	double indexCorrelation;
	amcostestimate_function amcostestimate = indexPath->indexinfo->amcostestimate;
	amcostestimate(root, indexPath, fakeLoopCount, &fakeIndexStartupCost,
				   &fakeIndexTotalCost, &indexSelectivity,
				   &indexCorrelation, &fakeIndexPages);

	Relation relation = RelationIdGetRelation(relationId);
	uint64 rowCount = ColumnarTableRowCount(relation);
	RelationClose(relation);
	double estimatedRows = rowCount * indexSelectivity;

	/*
	 * In the worst case (i.e no correlation between the column & the index),
	 * we need to read a different stripe for each row.
	 */
	double maxStripeReadCount = estimatedRows;

	/*
	 * In the best case (i.e the column is fully correlated with the index),
	 * we wouldn't read the same stripe again and again thanks
	 * to locality.
	 */
	double avgStripeRowCount =
		rowCount / (double) ColumnarTableStripeCount(relationId);
	double minStripeReadCount = estimatedRows / avgStripeRowCount;

	/*
	 * While being close to 0 means low correlation, being close to -1 or +1
	 * means high correlation. For index scans on columnar tables, it doesn't
	 * matter if the column and the index are "correlated" (+1) or
	 * "anti-correlated" (-1) since both help us avoiding from reading the
	 * same stripe again and again.
	 */
	double absIndexCorrelation = Abs(indexCorrelation);

	/*
	 * To estimate the number of stripes that we need to read, we do linear
	 * interpolation between minStripeReadCount & maxStripeReadCount. To do
	 * that, we use complement to 1 of absolute correlation, where being
	 * close to 0 means high correlation and being close to 1 means low
	 * correlation.
	 * In practice, we only want to do an index scan when absIndexCorrelation
	 * is 1 (or extremely close to it), or when the absolute number of tuples
	 * returned is very small. Other cases will have a prohibitive cost.
	 */
	double complementIndexCorrelation = 1 - absIndexCorrelation;
	double estimatedStripeReadCount =
		minStripeReadCount + complementIndexCorrelation * (maxStripeReadCount -
														   minStripeReadCount);

	Cost scanCost = perStripeCost * estimatedStripeReadCount;

	ereport(DEBUG4, (errmsg("re-costing index scan for columnar table: "
							"selectivity = %.10f, complement abs "
							"correlation = %.10f, per stripe cost = %.10f, "
							"estimated stripe read count = %.10f, "
							"total additional cost = %.10f",
							indexSelectivity, complementIndexCorrelation,
							perStripeCost, estimatedStripeReadCount,
							scanCost)));

	return scanCost;
}


/*
 * CostColumnarSeqPath sets costs given seq path for columnar table with
 * relationId.
 */
static void
CostColumnarSeqPath(RelOptInfo *rel, Oid relationId, Path *path)
{
	if (!enable_seqscan)
	{
		/* costs are already set to disable_cost, don't adjust them */
		return;
	}

	/*
	 * Seq scan doesn't support projection or qual pushdown, so we will read
	 * all the stripes and all the columns.
	 */
	double stripesToRead = ColumnarTableStripeCount(relationId);
	int numberOfColumnsRead = RelationIdGetNumberOfAttributes(relationId);

	path->startup_cost = 0;
	path->total_cost = stripesToRead *
					   ColumnarPerStripeScanCost(rel, relationId, numberOfColumnsRead);
}


/*
 * RelationIdGetNumberOfAttributes returns number of attributes that relation
 * with relationId has.
 */
static int
RelationIdGetNumberOfAttributes(Oid relationId)
{
	Relation relation = RelationIdGetRelation(relationId);
	int nattrs = relation->rd_att->natts;
	RelationClose(relation);
	return nattrs;
}


/*
 * CheckVarStats() checks whether a qual involving this Var is likely to be
 * useful based on the correlation stats. If so, or if stats are unavailable,
 * return true; otherwise return false.
 */
static bool
CheckVarStats(PlannerInfo *root, Var *var, Oid sortop)
{
	/*
	 * Collect isunique, ndistinct, and varCorrelation.
	 */
	VariableStatData varStatData;
	examine_variable(root, (Node *) var, var->varno, &varStatData);
	if (varStatData.rel == NULL ||
		!HeapTupleIsValid(varStatData.statsTuple))
	{
		return true;
	}

	AttStatsSlot sslot;
	if (!get_attstatsslot(&sslot, varStatData.statsTuple,
						  STATISTIC_KIND_CORRELATION, sortop,
						  ATTSTATSSLOT_NUMBERS))
	{
		ReleaseVariableStats(varStatData);
		return true;
	}

	Assert(sslot.nnumbers == 1);

	float4 varCorrelation = sslot.numbers[0];

	ReleaseVariableStats(varStatData);

	/*
	 * If the Var is not highly correlated, then the chunk's min/max bounds
	 * will be nearly useless.
	 */
	if (Abs(varCorrelation) < ColumnarQualPushdownCorrelation)
	{
		return false;
	}

	return true;
}


/*
 * CheckPushdownClause tests to see if clause is a candidate for pushing down
 * into the given rel (including join clauses). This test may not be exact in
 * all cases; it's used to reduce the search space for parameterization.
 *
 * Note that we don't try to handle cases like "Var + ExtParam = 3". That
 * would require going through eval_const_expression after parameter binding,
 * and that doesn't seem worth the effort. Here we just look for "Var op Expr"
 * or "Expr op Var", where Var references rel and Expr references other rels
 * (or no rels at all).
 */
static bool
CheckPushdownClause(PlannerInfo *root, RelOptInfo *rel, Expr *clause)
{
	if (IsA(clause, OpExpr))
	{
		OpExpr *opExpr = (OpExpr *) clause;
		Expr *lhs = list_nth(opExpr->args, 0);
		Expr *rhs = list_nth(opExpr->args, 1);

		Var *varSide;
		Expr *exprSide;
		if (IsA(lhs, Var) && ((Var *) lhs)->varno == rel->relid)
		{
			varSide = castNode(Var, lhs);
			exprSide = rhs;
		}
		else if (IsA(rhs, Var) && ((Var *) rhs)->varno == rel->relid)
		{
			varSide = castNode(Var, rhs);
			exprSide = lhs;
		}
		else
		{
			return false;
		}

		/* cannot push down a qual over the whole row */
		if (varSide->varattno <= 0)
		{
			return false;
		}

		if (contain_volatile_functions((Node *) exprSide))
		{
			return false;
		}

		/*
		 * Only the default opclass is used for qual pushdown.
		 */
		Oid varOpClass = GetDefaultOpClass(varSide->vartype, BTREE_AM_OID);
		Oid varOpFamily;
		Oid varOpcInType;

		if (!get_opclass_opfamily_and_input_type(varOpClass, &varOpFamily,
												 &varOpcInType))
		{
			return false;
		}

		Oid sortop = get_opfamily_member(varOpFamily, varOpcInType,
										 varOpcInType, BTLessStrategyNumber);

		Assert(OidIsValid(sortop));

		/*
		 * Check that statistics on the Var support the utility of this
		 * clause.
		 */
		if (!CheckVarStats(root, varSide, sortop))
		{
			return false;
		}

		/*
		 * Check that the exprSide doesn't reference the rel we are pushing
		 * into; e.g. "s = lower(s)".
		 */
		List *exprVars = pull_var_clause(
			(Node *) exprSide, PVC_RECURSE_AGGREGATES |
			PVC_RECURSE_WINDOWFUNCS | PVC_RECURSE_PLACEHOLDERS);
		ListCell *lc;
		foreach(lc, exprVars)
		{
			Var *var = (Var *) lfirst(lc);
			if (var->varno == rel->relid)
			{
				return false;
			}
		}

		return true;
	}

	return false;
}


/*
 * FilterPushdownClauses filters for clauses that are candidates for pushing
 * down into rel.
 */
static List *
FilterPushdownClauses(PlannerInfo *root, RelOptInfo *rel, List *inputClauses)
{
	List *filteredClauses = NIL;
	ListCell *lc;
	foreach(lc, inputClauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (rinfo->pseudoconstant ||
			!bms_is_member(rel->relid, rinfo->required_relids) ||
			!CheckPushdownClause(root, rel, rinfo->clause))
		{
			continue;
		}

		filteredClauses = lappend(filteredClauses, rinfo);
	}

	return filteredClauses;
}


static bool
PushdownJoinClauseMatches(PlannerInfo *root, RelOptInfo *rel,
						  EquivalenceClass *ec, EquivalenceMember *em,
						  void *arg)
{
	return true;
}


/*
 * FindPushdownJoinClauses finds join clauses, including those implied by ECs,
 * that may be pushed down.
 */
static List *
FindPushdownJoinClauses(PlannerInfo *root, RelOptInfo *rel)
{
	List *joinClauses = copyObject(rel->joininfo);

	/*
	 * XXX: Here we are generating the clauses just so we can later extract
	 * the interesting relids. This can probably be made more efficient.
	 */
	List *ecClauses = generate_implied_equalities_for_column(
		root, rel, PushdownJoinClauseMatches, NULL,
		rel->lateral_referencers);
	List *allClauses = list_concat(joinClauses, ecClauses);

	return FilterPushdownClauses(root, rel, allClauses);
}


/*
 * FindCandidateRelids identifies candidate rels for parameterization from the
 * list of join clauses.
 *
 * Some rels cannot be considered for parameterization, such as a partitioned
 * parent of the given rel. Other rels are just not useful because they don't
 * appear in a join clause that could be pushed down.
 */
static Relids
FindCandidateRelids(PlannerInfo *root, RelOptInfo *rel, List *joinClauses)
{
	Relids candidateRelids = NULL;
	ListCell *lc;
	foreach(lc, joinClauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		candidateRelids = bms_add_members(candidateRelids,
										  rinfo->required_relids);
	}

	candidateRelids = bms_del_member(candidateRelids, rel->relid);
	return candidateRelids;
}


/*
 * Combinations() calculates the number of combinations of n things taken k at
 * a time. When the correct result is large, the calculation may produce a
 * non-integer result, or overflow to inf, which caller should handle
 * appropriately.
 *
 * Use the following two formulae from Knuth TAoCP, 1.2.6:
 *    (2) Combinations(n, k) = (n*(n-1)..(n-k+1)) / (k*(k-1)..1)
 *    (5) Combinations(n, k) = Combinations(n, n-k)
 */
static double
Combinations(int n, int k)
{
	double v = 1;

	/*
	 * If k is close to n, then both the numerator and the denominator are
	 * close to n!, and we may overflow even if the input is reasonable
	 * (e.g. Combinations(500, 500)). Use formula (5) to choose the smaller,
	 * but equivalent, k.
	 */
	k = Min(k, n - k);

	/* calculate numerator of formula (2) first */
	for (int i = n; i >= n - k + 1; i--)
	{
		v *= i;
	}

	/*
	 * Divide by each factor in the denominator of formula (2), skipping
	 * division by 1.
	 */
	for (int i = k; i >= 2; i--)
	{
		v /= i;
	}

	return v;
}


/*
 * ChooseDepthLimit() calculates the depth limit for the parameterization
 * search, given the number of candidate relations.
 *
 * The maximum number of paths generated for a given depthLimit is:
 *
 *    Combinations(nCandidates, 0) + Combinations(nCandidates, 1) + ... +
 *    Combinations(nCandidates, depthLimit)
 *
 * There's no closed formula for a partial sum of combinations, so just keep
 * increasing the depth until the number of combinations exceeds the limit.
 */
static int
ChooseDepthLimit(int nCandidates)
{
	if (!EnableColumnarQualPushdown)
	{
		return 0;
	}

	int depth = 0;
	double numPaths = 1;

	while (depth < nCandidates)
	{
		numPaths += Combinations(nCandidates, depth + 1);

		if (numPaths > (double) ColumnarMaxCustomScanPaths)
		{
			break;
		}

		depth++;
	}

	return depth;
}


/*
 * AddColumnarScanPaths is the entry point for recursively generating
 * parameterized paths. See AddColumnarScanPathsRec() for discussion.
 */
static void
AddColumnarScanPaths(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte)
{
	List *joinClauses = FindPushdownJoinClauses(root, rel);
	Relids candidateRelids = FindCandidateRelids(root, rel, joinClauses);

	int depthLimit = ChooseDepthLimit(bms_num_members(candidateRelids));

	/* must always parameterize by lateral refs */
	Relids paramRelids = bms_copy(rel->lateral_relids);

	AddColumnarScanPathsRec(root, rel, rte, paramRelids, candidateRelids,
							depthLimit);
}


/*
 * AddColumnarScanPathsRec is a recursive function to search the
 * parameterization space and add CustomPaths for columnar scans.
 *
 * Columnar tables resemble indexes because of the ability to push down
 * quals. Ordinary quals, such as x = 7, can be pushed down easily. But join
 * quals of the form "x = y" (where "y" comes from another rel) require the
 * proper parameterization.
 *
 * Paths that require more outer rels can push down more join clauses that
 * depend on those outer rels. But requiring more outer rels gives the planner
 * fewer options for the shape of the plan. That means there is a trade-off,
 * and we should generate plans of various parameterizations, then let the
 * planner choose. We always need to generate one minimally-parameterized path
 * (parameterized only by lateral refs, if present) to make sure that at least
 * one path can be chosen. Then, we generate as many parameterized paths as we
 * reasonably can.
 *
 * The set of all possible parameterizations is the power set of
 * candidateRelids. The power set has cardinality 2^N, where N is the
 * cardinality of candidateRelids. To avoid creating a huge number of paths,
 * limit the depth of the search; the depthLimit is equivalent to the maximum
 * number of required outer rels (beyond the minimal parameterization) for the
 * path. A depthLimit of zero means that only the minimally-parameterized path
 * will be generated.
 */
static void
AddColumnarScanPathsRec(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte,
						Relids paramRelids, Relids candidateRelids,
						int depthLimit)
{
	AddColumnarScanPath(root, rel, rte, paramRelids);

	/* recurse for all candidateRelids, unless we hit the depth limit */
	Assert(depthLimit >= 0);
	if (depthLimit-- == 0)
	{
		return;
	}

	Relids tmpCandidateRelids = bms_copy(candidateRelids);
	int relid = -1;
	while ((relid = bms_next_member(candidateRelids, relid)) >= 0)
	{
		Relids tmpParamRelids = bms_add_member(
			bms_copy(paramRelids), relid);

		tmpCandidateRelids = bms_del_member(tmpCandidateRelids, relid);

		AddColumnarScanPathsRec(root, rel, rte, tmpParamRelids,
								tmpCandidateRelids, depthLimit);
	}

	bms_free(tmpCandidateRelids);
}


/*
 * Create and add a path with the given parameterization paramRelids.
 */
static void
AddColumnarScanPath(PlannerInfo *root, RelOptInfo *rel, RangeTblEntry *rte,
					Relids paramRelids)
{
	/*
	 * Must return a CustomPath, not a larger structure containing a
	 * CustomPath as the first field. Otherwise, nodeToString() will fail to
	 * output the additional fields.
	 */
	CustomPath *cpath = makeNode(CustomPath);

	cpath->methods = &ColumnarScanPathMethods;

	/*
	 * populate generic path information
	 */
	Path *path = &cpath->path;
	path->pathtype = T_CustomScan;
	path->parent = rel;
	path->pathtarget = rel->reltarget;

	/* columnar scans are not parallel-aware, but they are parallel-safe */
	path->parallel_safe = rel->consider_parallel;

	path->param_info = get_baserel_parampathinfo(root, rel, paramRelids);

	/*
	 * Now, baserestrictinfo contains the clauses referencing only this rel,
	 * and ppi_clauses (if present) represents the join clauses that reference
	 * this rel and rels contained in paramRelids (after accounting for
	 * ECs). Combine the two lists of clauses, extracting the actual clause
	 * from the rinfo, and filtering out pseudoconstants and SAOPs.
	 */
	List *allClauses = copyObject(rel->baserestrictinfo);
	if (path->param_info != NULL)
	{
		allClauses = list_concat(allClauses, path->param_info->ppi_clauses);
	}

	/*
	 * This is the set of clauses that can be pushed down for this
	 * parameterization (with the given paramRelids), and will be used to
	 * construct the CustomScan plan.
	 */
	List *pushdownClauses = FilterPushdownClauses(root, rel, allClauses);

	if (EnableColumnarQualPushdown)
	{
		cpath->custom_private = pushdownClauses;
	}

	int numberOfColumnsRead = bms_num_members(rte->selectedCols);

	CostColumnarScan(cpath, root, rel, rte->relid, numberOfColumnsRead,
					 list_length(cpath->custom_private));

	add_path(rel, path);
}


/*
 * CostColumnarScan calculates the cost of scanning the columnar table. The
 * cost is estimated by using all stripe metadata to estimate based on the
 * columns to read how many pages need to be read.
 */
static void
CostColumnarScan(CustomPath *cpath, PlannerInfo *root, RelOptInfo *rel,
				 Oid relationId, int numberOfColumnsRead, int nClauses)
{
	Path *path = &cpath->path;

	Selectivity clauseSel = clauselist_selectivity(
		root, cpath->custom_private, rel->relid, JOIN_INNER, NULL);

	/*
	 * We already filtered out clauses where the overall selectivity would be
	 * misleading, such as inequalities involving an uncorrelated column. So
	 * we can apply the selectivity directly to the number of stripes.
	 */
	double stripesToRead = clauseSel * ColumnarTableStripeCount(relationId);
	stripesToRead = Max(stripesToRead, 1.0);

	path->rows = rel->rows;
	path->startup_cost = 0;
	path->total_cost = stripesToRead *
					   ColumnarPerStripeScanCost(rel, relationId, numberOfColumnsRead);
}


/*
 * ColumnarPerStripeScanCost calculates the cost to scan a single stripe
 * of given columnar table based on number of columns that needs to be
 * read during scan operation.
 */
static Cost
ColumnarPerStripeScanCost(RelOptInfo *rel, Oid relationId, int numberOfColumnsRead)
{
	Relation relation = RelationIdGetRelation(relationId);
	List *stripeList = StripesForRelfilenode(relation->rd_node);
	RelationClose(relation);

	uint32 maxColumnCount = 0;
	uint64 totalStripeSize = 0;
	StripeMetadata *stripeMetadata = NULL;
	foreach_ptr(stripeMetadata, stripeList)
	{
		totalStripeSize += stripeMetadata->dataLength;
		maxColumnCount = Max(maxColumnCount, stripeMetadata->columnCount);
	}

	/*
	 * When no stripes are in the table we don't have a count in maxColumnCount. To
	 * prevent a division by zero turning into a NaN we keep the ratio on zero.
	 * This will result in a cost of 0 for scanning the table which is a reasonable
	 * cost on an empty table.
	 */
	if (maxColumnCount == 0)
	{
		return 0;
	}

	double columnSelectionRatio = numberOfColumnsRead / (double) maxColumnCount;
	Cost tableScanCost = (double) totalStripeSize / BLCKSZ * columnSelectionRatio;
	Cost perStripeScanCost = tableScanCost / list_length(stripeList);

	/*
	 * Finally, multiply the cost of reading a single stripe by seq page read
	 * cost to make our estimation scale compatible with postgres.
	 * Since we are calculating the cost for a single stripe here, we use seq
	 * page cost instead of random page cost. This is because, random page
	 * access only happens when switching between columns, which is pretty
	 * much neglactable.
	 */
	double relSpaceSeqPageCost;
	get_tablespace_page_costs(rel->reltablespace,
							  NULL, &relSpaceSeqPageCost);
	perStripeScanCost = perStripeScanCost * relSpaceSeqPageCost;

	return perStripeScanCost;
}


/*
 * ColumnarTableStripeCount returns the number of stripes that columnar
 * table with relationId has by using stripe metadata.
 */
static uint64
ColumnarTableStripeCount(Oid relationId)
{
	Relation relation = RelationIdGetRelation(relationId);
	List *stripeList = StripesForRelfilenode(relation->rd_node);
	int stripeCount = list_length(stripeList);
	RelationClose(relation);

	return stripeCount;
}


static Plan *
ColumnarScanPath_PlanCustomPath(PlannerInfo *root,
								RelOptInfo *rel,
								struct CustomPath *best_path,
								List *tlist,
								List *clauses,
								List *custom_plans)
{
	/*
	 * Must return a CustomScan, not a larger structure containing a
	 * CustomScan as the first field. Otherwise, copyObject() will fail to
	 * copy the additional fields.
	 */
	CustomScan *cscan = makeNode(CustomScan);

	cscan->methods = &ColumnarScanScanMethods;

	/* XXX: also need to store projected column list for EXPLAIN */

	if (EnableColumnarQualPushdown)
	{
		/*
		 * List of pushed-down clauses. The Vars referencing other relations
		 * will be changed into exec Params by create_customscan_plan().
		 *
		 * XXX: this just means what will be pushed into the columnar reader
		 * code; some of these may not be usable. We should fix this by
		 * passing down something more like ScanKeys, where we've already
		 * verified that the operators match the btree opclass of the chunk
		 * predicates.
		 */
		cscan->custom_exprs = copyObject(
			extract_actual_clauses(best_path->custom_private, false));
	}

	cscan->scan.plan.qual = extract_actual_clauses(clauses, false);
	cscan->scan.plan.targetlist = list_copy(tlist);
	cscan->scan.scanrelid = best_path->path.parent->relid;

	return (Plan *) cscan;
}


static Node *
ColumnarScan_CreateCustomScanState(CustomScan *cscan)
{
	ColumnarScanState *columnarScanState = (ColumnarScanState *) newNode(
		sizeof(ColumnarScanState), T_CustomScanState);

	CustomScanState *cscanstate = &columnarScanState->custom_scanstate;
	cscanstate->methods = &ColumnarScanExecuteMethods;

	return (Node *) cscanstate;
}


static Node *
EvalParamsMutator(Node *node, ExprContext *econtext)
{
	if (node == NULL)
	{
		return NULL;
	}

	if (IsA(node, Param))
	{
		Param *param = (Param *) node;
		int16 typLen;
		bool typByVal;
		bool isnull;

		get_typlenbyval(param->paramtype, &typLen, &typByVal);

		/* XXX: should save ExprState for efficiency */
		ExprState *exprState = ExecInitExprWithParams((Expr *) node,
													  econtext->ecxt_param_list_info);
		Datum pval = ExecEvalExpr(exprState, econtext, &isnull);

		return (Node *) makeConst(param->paramtype,
								  param->paramtypmod,
								  param->paramcollid,
								  (int) typLen,
								  pval,
								  isnull,
								  typByVal);
	}

	return expression_tree_mutator(node, EvalParamsMutator, (void *) econtext);
}


/*
 * EvaluateClauseParams simply replaces Params with Consts in clauses using
 * econtext.
 */
static List *
EvaluateClauseParams(ExprContext *econtext, List *clauses)
{
	return (List *) expression_tree_mutator(
		(Node *) clauses, EvalParamsMutator, econtext);
}


static void
ColumnarScan_BeginCustomScan(CustomScanState *cscanstate, EState *estate, int eflags)
{
	CustomScan *cscan = (CustomScan *) cscanstate->ss.ps.plan;
	ColumnarScanState *columnarScanState = (ColumnarScanState *) cscanstate;
	ExprContext *stdecontext = cscanstate->ss.ps.ps_ExprContext;

	/*
	 * Make a new ExprContext just like the existing one, except that we don't
	 * reset it every tuple.
	 */
	ExecAssignExprContext(estate, &cscanstate->ss.ps);
	columnarScanState->css_RuntimeContext = cscanstate->ss.ps.ps_ExprContext;
	cscanstate->ss.ps.ps_ExprContext = stdecontext;

	/* XXX: separate into runtime clauses and normal clauses */
	ResetExprContext(columnarScanState->css_RuntimeContext);
	columnarScanState->qual = EvaluateClauseParams(
		columnarScanState->css_RuntimeContext, cscan->custom_exprs);

	/* scan slot is already initialized */
}


static Bitmapset *
ColumnarAttrNeeded(ScanState *ss)
{
	TupleTableSlot *slot = ss->ss_ScanTupleSlot;
	int natts = slot->tts_tupleDescriptor->natts;
	Bitmapset *attr_needed = NULL;
	Plan *plan = ss->ps.plan;
	int flags = PVC_RECURSE_AGGREGATES |
				PVC_RECURSE_WINDOWFUNCS | PVC_RECURSE_PLACEHOLDERS;
	List *vars = list_concat(pull_var_clause((Node *) plan->targetlist, flags),
							 pull_var_clause((Node *) plan->qual, flags));
	ListCell *lc;

	foreach(lc, vars)
	{
		Var *var = lfirst(lc);

		if (var->varattno < 0)
		{
			ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							errmsg(
								"UPDATE and CTID scans not supported for ColumnarScan")));
		}

		if (var->varattno == 0)
		{
			elog(DEBUG1, "Need attribute: all");

			/* all attributes are required, we don't need to add more so break*/
			attr_needed = bms_add_range(attr_needed, 0, natts - 1);
			break;
		}

		elog(DEBUG1, "Need attribute: %d", var->varattno);
		attr_needed = bms_add_member(attr_needed, var->varattno - 1);
	}

	return attr_needed;
}


static TupleTableSlot *
ColumnarScanNext(ColumnarScanState *columnarScanState)
{
	CustomScanState *node = (CustomScanState *) columnarScanState;

	/*
	 * get information from the estate and scan state
	 */
	TableScanDesc scandesc = node->ss.ss_currentScanDesc;
	EState *estate = node->ss.ps.state;
	ScanDirection direction = estate->es_direction;
	TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;

	if (scandesc == NULL)
	{
		/* the columnar access method does not use the flags, they are specific to heap */
		uint32 flags = 0;
		Bitmapset *attr_needed = ColumnarAttrNeeded(&node->ss);

		/*
		 * We reach here if the scan is not parallel, or if we're serially
		 * executing a scan that was planned to be parallel.
		 */
		scandesc = columnar_beginscan_extended(node->ss.ss_currentRelation,
											   estate->es_snapshot,
											   0, NULL, NULL, flags, attr_needed,
											   columnarScanState->qual);
		bms_free(attr_needed);

		node->ss.ss_currentScanDesc = scandesc;
	}

	/*
	 * get the next tuple from the table
	 */
	if (table_scan_getnextslot(scandesc, direction, slot))
	{
		return slot;
	}
	return NULL;
}


/*
 * SeqRecheck -- access method routine to recheck a tuple in EvalPlanQual
 */
static bool
ColumnarScanRecheck(ColumnarScanState *node, TupleTableSlot *slot)
{
	return true;
}


static TupleTableSlot *
ColumnarScan_ExecCustomScan(CustomScanState *node)
{
	return ExecScan(&node->ss,
					(ExecScanAccessMtd) ColumnarScanNext,
					(ExecScanRecheckMtd) ColumnarScanRecheck);
}


static void
ColumnarScan_EndCustomScan(CustomScanState *node)
{
	/*
	 * get information from node
	 */
	TableScanDesc scanDesc = node->ss.ss_currentScanDesc;

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->ss.ps);

	/*
	 * clean out the tuple table
	 */
	if (node->ss.ps.ps_ResultTupleSlot)
	{
		ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	}
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/*
	 * close heap scan
	 */
	if (scanDesc != NULL)
	{
		table_endscan(scanDesc);
	}
}


static void
ColumnarScan_ReScanCustomScan(CustomScanState *node)
{
	CustomScan *cscan = (CustomScan *) node->ss.ps.plan;
	ColumnarScanState *columnarScanState = (ColumnarScanState *) node;

	ResetExprContext(columnarScanState->css_RuntimeContext);
	columnarScanState->qual = EvaluateClauseParams(
		columnarScanState->css_RuntimeContext, cscan->custom_exprs);

	TableScanDesc scanDesc = node->ss.ss_currentScanDesc;

	if (scanDesc != NULL)
	{
		/* XXX: hack to pass quals as scan keys */
		ScanKey scanKeys = (ScanKey) columnarScanState->qual;
		table_rescan(node->ss.ss_currentScanDesc,
					 scanKeys);
	}
}


static void
ColumnarScan_ExplainCustomScan(CustomScanState *node, List *ancestors,
							   ExplainState *es)
{
	TableScanDesc scanDesc = node->ss.ss_currentScanDesc;

	if (scanDesc != NULL)
	{
		CustomScan *cscan = castNode(CustomScan, node->ss.ps.plan);
		List *chunkGroupFilter = cscan->custom_exprs;

		if (chunkGroupFilter != NIL)
		{
			Expr *conjunction;

			if (list_length(chunkGroupFilter) == 1)
			{
				conjunction = (Expr *) linitial(chunkGroupFilter);
			}
			else
			{
				conjunction = make_andclause(chunkGroupFilter);
			}

#if PG_VERSION_NUM >= 130000
			List *context = set_deparse_context_plan(es->deparse_cxt,
													 &cscan->scan.plan,
													 ancestors);
#else
			PlanState *planstate = &node->ss.ps;
			List *context = set_deparse_context_planstate(es->deparse_cxt,
														  (Node *) planstate,
														  ancestors);
#endif

			char *str = deparse_expression((Node *) conjunction,
										   context, false, false);
			ExplainPropertyText("Columnar Chunk Group Filters", str, es);

			ExplainPropertyInteger(
				"Columnar Chunk Groups Removed by Filter",
				NULL, ColumnarScanChunkGroupsFiltered(scanDesc), es);
		}
	}
}
