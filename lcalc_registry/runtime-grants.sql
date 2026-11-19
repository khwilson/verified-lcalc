-- Run with the schema owner after migrations. Create registry_runtime separately,
-- with a secret password obtained through your deployment's secret manager.
-- These grants assume the default public schema; adapt for another schema.
GRANT USAGE ON SCHEMA public TO registry_runtime;
GRANT SELECT, INSERT ON ALL TABLES IN SCHEMA public TO registry_runtime;
GRANT UPDATE ON registry_task, registry_schedule TO registry_runtime;
REVOKE ALL ON registry_schema_version FROM registry_runtime;
GRANT SELECT ON registry_schema_version TO registry_runtime;
-- No UPDATE or DELETE on immutable evidence. The owner-installed triggers also
-- reject those operations if broader grants are accidentally introduced.
