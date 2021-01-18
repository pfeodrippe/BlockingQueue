\*  TRACE EXPRESSION: _traceExpression_1 = buffer \o << 2, 21 >>
---- MODULE TE ----
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
