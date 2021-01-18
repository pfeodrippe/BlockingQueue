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
