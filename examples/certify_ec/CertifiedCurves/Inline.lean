module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- Inline exact JSON is also supported; there is no external build input.
certify_ec InlineCurve from_json_string r#"{"schema":"lcalc.ec-rank.v1","subject":{"ainvs":["0","-1","1","-10","-20"],"conductor":"11"},"parameters":{"precision_bits":"53","terms":"1","steps_per_unit":"0","cutoff":"0"},"rank":"0","coefficients":["1"],"arithmetic":{"minimality":["11","11","11","11","11"],"at_two":null,"at_three":null},"enclosure":{"real":["366028917649787835048376743221/13418806384615817897124636393472","963345890145134125303004031503/1677350798076977237140579549184"],"imag":["0/1","0/1"]},"evaluator":{"alpha":["5397215081808807583435051761664/2848959001535859775543212890625","337325942613050473965764476928/178059937595991230010986328125"],"tail":"28674758607465946046101926841/104834424879811077321286221824","geometric_upper":"169336229459221/1125899906842624"}}"#
