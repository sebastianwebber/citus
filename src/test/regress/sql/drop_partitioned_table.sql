--
-- DROP_PARTITIONED_TABLE
--
-- Tests to make sure that we properly drop distributed partitioned tables
--

SET citus.next_shard_id TO 720000;
SET citus.shard_count TO 4;
SET citus.shard_replication_factor TO 1;
CREATE SCHEMA drop_partitioned_table;
SET search_path = drop_partitioned_table;

-- create a function that allows us to see the values of
-- original and normal values for each dropped table
-- coming from pg_event_trigger_dropped_objects()
-- for now the only case where we can distinguish a
-- dropped partition because of its dropped parent
-- is when both values are false: check citus_drop_trigger

CREATE FUNCTION check_original_normal_values()
    RETURNS event_trigger LANGUAGE plpgsql AS $$
DECLARE
    v_obj record;
BEGIN
    FOR v_obj IN SELECT * FROM pg_event_trigger_dropped_objects()
        WHERE object_type IN ('table', 'foreign table')
    LOOP
	    RAISE NOTICE 'dropped object: %.% original: % normal: %',
            v_obj.schema_name,
            v_obj.object_name,
            v_obj.original,
            v_obj.normal;
    END LOOP;
END;
$$;

CREATE EVENT TRIGGER new_trigger_for_drops
   ON sql_drop
   EXECUTE FUNCTION check_original_normal_values();

-- CASE 1
-- Dropping the parent table
CREATE TABLE parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
CREATE TABLE child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
SELECT create_distributed_table('parent','x');

\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP TABLE parent;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table;
\d

\c - - - :master_port
SET search_path = drop_partitioned_table;
SET citus.next_shard_id TO 720000;

-- CASE 2
-- Dropping the parent table, but including children in the DROP command
CREATE TABLE parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
CREATE TABLE child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
SELECT create_distributed_table('parent','x');

\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP TABLE child1, parent, child2;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table;
\d

\c - - - :master_port
SET search_path = drop_partitioned_table;
SET citus.next_shard_id TO 720000;

-- CASE 3
-- DROP OWNED BY role1; Only parent is owned by role1, children are owned by another owner
CREATE ROLE role1;
SELECT run_command_on_workers('CREATE ROLE role1');
GRANT ALL ON SCHEMA drop_partitioned_table TO role1;
SET ROLE role1;
CREATE TABLE drop_partitioned_table.parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
RESET ROLE;
CREATE TABLE child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE parent ATTACH PARTITION child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
SELECT create_distributed_table('parent','x');

\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP OWNED BY role1;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table;
\d

\c - - - :master_port
SET search_path = drop_partitioned_table;
SET citus.next_shard_id TO 720000;

-- CASE 4
-- DROP OWNED BY role1; Parent and children are owned by role1
GRANT ALL ON SCHEMA drop_partitioned_table TO role1;
SET ROLE role1;
CREATE TABLE drop_partitioned_table.parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
CREATE TABLE drop_partitioned_table.child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE drop_partitioned_table.parent ATTACH PARTITION drop_partitioned_table.child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE drop_partitioned_table.child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE drop_partitioned_table.parent ATTACH PARTITION drop_partitioned_table.child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
RESET ROLE;
SELECT create_distributed_table('parent','x');

\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP OWNED BY role1;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table;
\d

\c - - - :master_port
SET search_path = drop_partitioned_table;
SET citus.next_shard_id TO 720000;
REVOKE ALL ON SCHEMA drop_partitioned_table FROM role1;
DROP ROLE role1;
SELECT run_command_on_workers('DROP ROLE role1');

-- CASE 5
-- DROP SCHEMA schema1 CASCADE; Parent is in schema1, children are in another schema
CREATE SCHEMA schema1;
CREATE TABLE schema1.parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
CREATE TABLE child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE schema1.parent ATTACH PARTITION child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE schema1.parent ATTACH PARTITION child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
SELECT create_distributed_table('schema1.parent','x');

SET search_path = drop_partitioned_table, schema1;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP SCHEMA schema1 CASCADE;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table, schema1;
\d

\c - - - :master_port
SET citus.next_shard_id TO 720000;
-- CASE 6
-- DROP SCHEMA schema1 CASCADE; Parent and children are in schema1
CREATE SCHEMA schema1;
CREATE TABLE schema1.parent (x text, t timestamptz DEFAULT now()) PARTITION BY RANGE (t);
CREATE TABLE schema1.child1 (x text, t timestamptz DEFAULT now());
ALTER TABLE schema1.parent ATTACH PARTITION schema1.child1 FOR VALUES FROM ('2021-05-31') TO ('2021-06-01');
CREATE TABLE schema1.child2 (x text, t timestamptz DEFAULT now());
ALTER TABLE schema1.parent ATTACH PARTITION schema1.child2 FOR VALUES FROM ('2021-06-30') TO ('2021-07-01');
SELECT create_distributed_table('schema1.parent','x');

SET search_path = drop_partitioned_table, schema1;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;
\set VERBOSITY terse
DROP SCHEMA schema1 CASCADE;
\d
SELECT logicalrelid, shardid FROM pg_dist_shard WHERE shardid >= 720000 AND shardid < 730000 ORDER BY shardid;

\c - - - :worker_1_port
SET search_path = drop_partitioned_table, schema1;
\d

\c - - - :master_port
SET search_path = drop_partitioned_table;

DROP SCHEMA drop_partitioned_table CASCADE;
SELECT run_command_on_workers('DROP SCHEMA IF EXISTS drop_partitioned_table CASCADE');
SET search_path TO public;
