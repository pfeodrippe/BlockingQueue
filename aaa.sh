# java -cp /Users/paulo.feodrippe/dev/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar -XX:+UseParallelGC tlc2.TLC -generateSpecTE BlockingQueue.tla -tool -modelcheck -coverage 1 -config BlockingQueue.cfg > BlockingQueue.out

java -cp /Users/paulo.feodrippe/dev/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar tlc2.TraceExplorer -overwrite -traceExpressions -expressionsFile eita.out BlockingQueue ; \
    cat TE.tla TTrace.tla > Eita.tla && \
        mv Eita.tla TE.tla && \
        sed -i"..." '/^EXTENDS.*/a\
 CONSTANTS p1, p2, p3, p4' TE.tla && \
        sed '/^CONSTANTS/r'<(
    echo "p1 = p1"
    echo "p2 = p2"
    echo "p3 = p3"
    echo "p4 = p4"
) TE.cfg > /tmp/TE.cfg && \
        cp /tmp/TE.cfg TE.cfg && \
        sed -i "..." 's/TTraceExpression//' TE.cfg && \
        sed -i"..." 's/ALIAS//' TE.cfg && \
        rm TTrace.tla && \
        rm TTrace.cfg && \
        java -cp /Users/paulo.feodrippe/dev/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar:CommunityModules.jar -XX:+UseParallelGC tlc2.TLC -noGenerateSpecTE -tool TE.tla -config TE.cfg
