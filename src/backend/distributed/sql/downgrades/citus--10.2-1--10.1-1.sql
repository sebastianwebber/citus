-- citus--10.2-1--10.1-1

#include "../../../columnar/sql/downgrades/columnar--10.2-1--10.1-1.sql"

DROP FUNCTION pg_catalog.stop_metadata_sync_to_node(text, integer, bool);

CREATE FUNCTION pg_catalog.stop_metadata_sync_to_node(nodename text, nodeport integer)
	RETURNS VOID
	LANGUAGE C STRICT
	AS 'MODULE_PATHNAME', $$stop_metadata_sync_to_node$$;
COMMENT ON FUNCTION pg_catalog.stop_metadata_sync_to_node(nodename text, nodeport integer)
    IS 'stop metadata sync to node';

DROP FUNCTION pg_catalog.citus_internal_add_partition_metadata(regclass, "char", text, integer, "char");
DROP FUNCTION pg_catalog.citus_internal_add_shard_metadata(regclass, bigint, "char", text, text);
DROP FUNCTION pg_catalog.citus_internal_add_placement_metadata(bigint, integer, bigint, integer, bigint);
DROP FUNCTION pg_catalog.citus_internal_update_placement_metadata(bigint, integer, integer);
DROP FUNCTION pg_catalog.citus_internal_delete_shard_metadata(bigint);
DROP FUNCTION pg_catalog.citus_internal_update_relation_colocation(oid, integer);

REVOKE ALL ON FUNCTION pg_catalog.worker_record_sequence_dependency(regclass,regclass,name) FROM PUBLIC;
ALTER TABLE pg_catalog.pg_dist_placement DROP CONSTRAINT placement_shardid_groupid_unique_index;
