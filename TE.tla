\*  TRACE EXPRESSION: _traceExpression_1 = buffer \o << 2, 21 >>
---- MODULE TE ----
EXTENDS TTrace, TLC

VARIABLES traceExpression_1

_TEInit ==
    /\ _SpecTEInit
    /\ traceExpression_1 = (buffer \o << 2, 21 >>)

----

_TENext ==
    /\ _SpecTENext
    /\ traceExpression_1' = (buffer' \o << 2, 21 >>)

----
\* Generated on Mon Jan 18 13:08:46 BRT 2021
=============================================================================
