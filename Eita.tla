\*  TRACE EXPRESSION: _traceExpression_1 = buffer \o << 2, 21 >>
---- MODULE Eita ----
EXTENDS TTrace, TLC

VARIABLES _traceExpression_1

\* INIT definition @teBehaviorInit:0
_TEInit ==
    /\ _SpecTEInit
    /\ _traceExpression_1 = (buffer \o << 2, 21 >>)

----
\* NEXT definition @teBehaviorNext:0
_TENext ==
    /\ _SpecTENext
    /\ _traceExpression_1' = (buffer \o << 2, 21 >>)

----
\* Generated on Mon Jan 18 15:54:17 BRT 2021
=============================================================================
---- MODULE TTrace ----
EXTENDS BlockingQueue, Toolbox, TLC

\* TE declaration
TTraceExpression ==
    LET BlockingQueue_TE == INSTANCE BlockingQueue_TE
    IN BlockingQueue_TE!TraceExpression

\* TraceDef definition
TTraceTraceDef == INSTANCE TTraceTraceDef
def_ov_16109960574722000 == TTraceTraceDef!def_ov_16109960574722000

\* PROPERTY definition
prop_16109960574723000 ==
~(([]<>(
    buffer = (
    <<"p2", "p3">>
    )    /\
    waitSet = (
    {"p1"}
    )
))/\([]<>(
    buffer = (
    <<"p2", "p3", "p2">>
    )    /\
    waitSet = (
    {"p1"}
    )
)))
----

\* TRACE INIT definition traceExploreInit
_SpecTEInit ==
    /\ buffer = _TETrace[1].buffer
    /\ waitSet = _TETrace[1].waitSet

----

\* TRACE NEXT definition traceExploreNext
_SpecTENext ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ j = i + 1
           \/ /\ i = 13
              /\ j = 5
        /\ buffer  = _TETrace[i].buffer
        /\ buffer' = _TETrace[j].buffer
        /\ waitSet  = _TETrace[i].waitSet
        /\ waitSet' = _TETrace[j].waitSet


=============================================================================



---- MODULE BlockingQueue_TE ----
EXTENDS BlockingQueue, Toolbox, TLC

TraceExpression == 
    [
        buffer |-> buffer
        ,waitSet |-> waitSet
        \* Put additional trace expressions here; examples:
        \* ,x |-> ~y'
        \* ,e |-> ENABLED ActionName
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to deserialize the trace from a binary file.
 To create the file, replace your spec's invariant F with:
  Inv == IF F THEN TRUE ELSE ~IOSerialize(Trace, "file.bin", TRUE)
 (IOUtils and TLCExt modules from https://modules.tlapl.us/)
\*
\*---- MODULE TTraceTraceDef ----
\*EXTENDS BlockingQueue, IOUtils, Toolbox, TLC
\*
\*def_ov_16109960574722000 == IODeserialize("file.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TTraceTraceDef ----
EXTENDS BlockingQueue, Toolbox, TLC

def_ov_16109960574722000 == 
    <<
    ([buffer |-> <<>>,waitSet |-> {}]),
    ([buffer |-> <<"p2">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p3">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p3", "p2">>,waitSet |-> {}]),
    ([buffer |-> <<"p2", "p3", "p2">>,waitSet |-> {"p1"}]),
    ([buffer |-> <<"p2", "p3", "p2">>,waitSet |-> {"p1", "p3"}]),
    ([buffer |-> <<"p2", "p3", "p2">>,waitSet |-> {"p1", "p3", "p4"}]),
    ([buffer |-> <<"p2", "p3", "p2">>,waitSet |-> {"p1", "p2", "p3", "p4"}]),
    ([buffer |-> <<"p3", "p2">>,waitSet |-> {"p1", "p3", "p4"}]),
    ([buffer |-> <<"p3", "p2", "p2">>,waitSet |-> {"p1", "p3", "p4"}]),
    ([buffer |-> <<"p2", "p2">>,waitSet |-> {"p1", "p3"}]),
    ([buffer |-> <<"p2">>,waitSet |-> {"p1"}]),
    ([buffer |-> <<"p2", "p3">>,waitSet |-> {"p1"}])
    >>
----


=============================================================================
