module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

certify_ec Curve11 from_json "../../../data/witnesses/11a1.json"
certify_ec Curve37 from_json "../../../data/witnesses/37a1.json"
certify_ec Curve112 from_json "../../../data/witnesses/112a2.json"
