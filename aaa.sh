java -cp /Users/paulo.feodrippe/dev/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TraceExplorer -overwrite -traceExpressions -expressionsFile eita.out BlockingQueue ; \
    cat TE.tla TTrace.tla > Eita.tla && \
        mv Eita.tla TE.tla && \
        sed -i '/^EXTENDS.*/a\
 CONSTANTS p1, p2, p3, p4' TE.tla && \
        rm TTrace.tla && \
        rm TTrace.cfg && \
        java -cp /Users/paulo.feodrippe/dev/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar:CommunityModules.jar -XX:+UseParallelGC tlc2.TLC -noGenerateSpecTE -tool TE.tla -config TE.cfg
