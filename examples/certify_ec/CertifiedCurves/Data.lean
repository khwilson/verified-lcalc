module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Explicit prime/value pairs from ec_classdata, including the bad prime.
-- These are arithmetic certificates, independent of analytic rank.
certify_ec Data11 from_json "../../../data/curve-data/11a1.json"
certify_ec Data37 from_json "../../../data/curve-data/37a1.json"
