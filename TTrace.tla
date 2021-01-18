---- MODULE TTrace ----
EXTENDS BlockingQueue, Toolbox, TLC

\* TE declaration
TTraceExpression ==
    LET BlockingQueue_TE == INSTANCE BlockingQueue_TE
    IN BlockingQueue_TE!TraceExpression

\* TraceDef definition
TTraceTraceDef == INSTANCE TTraceTraceDef
def_ov_16109861263822000 == TTraceTraceDef!def_ov_16109861263822000

\* PROPERTY definition
prop_16109861263833000 ==
~(([]<>(
    buffer = (
    <<"p2", "p2">>
    )    /\
    waitSet = (
    {"p1"}
    )
))/\([]<>(
    buffer = (
    <<"p2", "p2", "p4">>
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





Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to deserialize the trace from a binary file.
 To create the file, replace your spec's invariant F with:
  Inv == IF F THEN TRUE ELSE ~IOSerialize(Trace, "file.bin", TRUE)
 (IOUtils and TLCExt modules from https://modules.tlapl.us/)
\*
\*---- MODULE TTraceTraceDef ----
\*EXTENDS BlockingQueue, IOUtils, Toolbox, TLC
\*
\*def_ov_16109861263822000 == IODeserialize("file.bin", TRUE)
\*
\*=============================================================================
\*

