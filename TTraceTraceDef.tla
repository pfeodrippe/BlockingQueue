---- MODULE TTraceTraceDef ----
EXTENDS BlockingQueue, Toolbox, TLC

def_ov_16109861263822000 == 
    <<
    ([buffer |-> <<>>,waitSet |-> {}]),
    ([buffer |-> <<"p2">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p2">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p2", "p4">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p2", "p4">>,waitSet |-> {"p1"}]),
    ([buffer |-> <<"p2", "p2", "p4">>,waitSet |-> {"p1", "p3"}]),
    ([buffer |-> <<"p2", "p2", "p4">>,waitSet |-> {"p1", "p2", "p3"}]),
    ([buffer |-> <<"p2", "p2", "p4">>,waitSet |-> {"p1", "p2", "p3", "p4"}]),
    ([buffer |-> <<"p2", "p4">>,waitSet |-> {"p1", "p3", "p4"}]),
    ([buffer |-> <<"p4">>,waitSet |-> {"p1", "p4"}]),
    ([buffer |-> <<>>,waitSet |-> {"p1"}]),
    ([buffer |-> <<"p2">>,waitSet |-> {"p1"}]),
    ([buffer |-> <<"p2", "p2">>,waitSet |-> {"p1"}])
    >>
----


=============================================================================
