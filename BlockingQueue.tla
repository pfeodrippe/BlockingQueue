--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

a <: b == a

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ConstInit ==
  /\ Producers \in (SUBSET {"p1","p2","p3","p4"} \ {({} <: {STRING})})
  /\ Consumers \in (SUBSET {"c1","c2","c3"} \ {({} <: {STRING})})
  /\ BufCapacity = 1

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)
       
-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

(* @see java.lang.Object#notify *)       
Notify == IF waitSet # ({} <: {STRING}) \* {}
          THEN \E x \in waitSet: waitSet' = waitSet \ {x}
          ELSE UNCHANGED waitSet

(* @see java.lang.Object#wait *)
Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
   \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ Notify
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
   \/ /\ buffer # <<>> <: Seq(STRING) \* <<>>
      /\ buffer' = Tail(buffer)
      /\ Notify
   \/ /\ buffer = <<>> <: Seq(STRING) \*
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = (<<>> <: Seq(STRING))
        /\ waitSet = ({} <: {STRING})

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \E t \in RunningThreads: \/ /\ t \in Producers
                                    /\ Put(t, t) \* Add some data to buffer
                                 \/ /\ t \in Consumers
                                    /\ Get(t)

-----------------------------------------------------------------------------

(* TLA+ is untyped, thus lets verify the range of some values in each state. *)
TypeInv == /\ buffer \in Seq(Producers)
           /\ Len(buffer) \in 0..BufCapacity
           /\ waitSet \subseteq (Producers \cup Consumers)

(* No Deadlock *)
Invariant == waitSet # (Producers \cup Consumers)

=============================================================================


markus@avocado:~/src/TLA/_community/apalache(ik/multicore)$ git log -n1
commit ab39edc8f6c301fa254a43fb854427d9a3cf8a2d (HEAD -> ik/multicore, origin/ik/multicore)
Author: Igor Konnov <igor@interchain.io>
Date:   Sun Jan 19 14:46:53 2020 +0100

    preemptive split upon timeout

markus@avocado:~/src/TLA/_community/apalache(ik/multicore)$ java --version
openjdk 11.0.5 2019-10-15
OpenJDK Runtime Environment (build 11.0.5+10-post-Ubuntu-0ubuntu1.118.04)
OpenJDK 64-Bit Server VM (build 11.0.5+10-post-Ubuntu-0ubuntu1.118.04, mixed mode, sharing)

markus@avocado:~/src/TLA/_community/apalache(ik/multicore)$ export LD_LIBRARY_PATH="$LD_LIBRARY_PATH":/home/markus/src/TLA/_community/apalache/3rdparty/lib

markus@avocado:~/src/TLA/_community/apalache(ik/multicore)$ time bin/apalache-mc check --init=Init --cinit=ConstInit --next=Next --length=50 --inv=Inv --nworkers=4 --debug BlockingQueue.tla
# Tool home: /home/markus/src/TLA/_community/apalache
# Package:   /home/markus/src/TLA/_community/apalache/apalache-pkg-0.6.0-SNAPSHOT-full.jar
# JVM args: -Xmx4096m
#
# APALACHE version 0.6.0-SNAPSHOT build 0.5.0-289-gab39edc
#
# WARNING: This tool is in the experimental stage.
#          Please report bugs at: [https://github.com/konnov/apalache/issues]

Checker options: filename=BlockingQueue.tla, init=Init, next=Next, inv=Inv I@092202.699
WARNING: An illegal reflective access operation has occurred
WARNING: Illegal reflective access by com.google.inject.internal.cglib.core.$ReflectUtils$1 (file:/home/markus/src/TLA/_community/apalache/apalache-pkg-0.6.0-SNAPSHOT-full.jar) to method java.lang.ClassLoader.defineClass(java.lang.String,byte[],int,int,java.security.ProtectionDomain)
WARNING: Please consider reporting this to the maintainers of com.google.inject.internal.cglib.core.$ReflectUtils$1
WARNING: Use --illegal-access=warn to enable warnings of further illegal reflective access operations
WARNING: All illegal access operations will be denied in a future release
PASS #0: SanyParser                                                 I@092203.136
Parsing file /home/markus/src/TLA/_community/apalache/BlockingQueue.tla
Parsing file /tmp/Naturals.tla
Parsing file /tmp/Sequences.tla
Parsing file /tmp/FiniteSets.tla
PASS #1: ConfigurationPass                                          I@092203.488
PASS #2: InlinePass                                                 I@092203.516
  > InlinerOfUserOper                                               I@092203.522
  > LetInExpander                                                   I@092203.543
PASS #3: PrimingPass                                                I@092203.574
  > Introducing ConstInitPrimed for ConstInit'                      I@092203.577
  > Introducing InitPrimed for Init'                                I@092203.581
PASS #4: VCGen                                                      I@092203.608
  > Producing verification conditions from the invariant Inv        I@092203.608
  > VCGen produced 1 verification condition(s)                      I@092203.609
PASS #5: PreprocessingPass                                          I@092203.632
  > Before preprocessing: unique renaming                           I@092203.632
 > Applying standard transformations:                               I@092203.639
  > Desugarer                                                       I@092203.640
  > UniqueRenamer                                                   I@092203.653
  > Normalizer                                                      I@092203.702
  > Keramelizer                                                     I@092203.708
  > PrimedEqualityToMembership                                      I@092203.728
  > After preprocessing: UniqueRenamer                              I@092203.731
PASS #6: TransitionFinderPass                                       I@092203.787
  > Found 1 initializing transitions                                I@092203.898
  > Found 6 transitions                                             I@092203.969
  > Found constant initializer ConstInit                            I@092203.969
  > Applying unique renaming                                        I@092203.970
PASS #7: OptimizationPass                                           I@092204.007
 > Applying optimizations:                                          I@092204.014
  > ExprOptimizer                                                   I@092204.016
  > ConstSimplifier                                                 I@092204.025
PASS #8: AnalysisPass                                               I@092204.046
  > Introduced expression grades                                    I@092204.067
  > Found 8 skolemizable existentials                               I@092204.068
  > Introduced 31 formula hints                                     I@092204.069
PASS #9: BoundedChecker                                             I@092204.070
Worker 2 is initializing                                            I@092204.168
Worker 4 is initializing                                            I@092204.168
Worker 3 is initializing                                            I@092204.168
Worker 1 is initializing                                            I@092204.168
Worker 1: Initializing CONSTANTS with the provided operator         I@092204.173
Worker 1 started                                                    I@092204.250
Worker 4 started                                                    I@092204.250
Worker 3 started                                                    I@092204.250
Worker 2 started                                                    I@092204.250
Worker 1: CLOSING NODE 0                                            I@092204.341
Worker 1: Step 0, level 0: collecting 1 enabled transition(s)       I@092204.370
Worker 1: INTRODUCED NODE 1 with 6 open transitions                 I@092204.391
Worker 1: CLOSING NODE 1                                            I@092204.857
Worker 1: Step 1, level 0: collecting 2 enabled transition(s)       I@092204.890
Worker 1: INTRODUCED NODE 2 with 6 open transitions                 I@092204.981
Worker 3: CLOSING NODE 2                                            I@092205.423
Worker 3: Step 2, level 0: collecting 4 enabled transition(s)       I@092205.482
Worker 3: INTRODUCED NODE 3 with 6 open transitions                 I@092205.582
Worker 2: CLOSING NODE 3                                            I@092206.075
Worker 2: Step 3, level 0: collecting 4 enabled transition(s)       I@092206.152
Worker 2: INTRODUCED NODE 4 with 6 open transitions                 I@092206.263
Worker 1: CLOSING NODE 4                                            I@092206.813
Worker 1: Step 4, level 0: collecting 6 enabled transition(s)       I@092206.873
Worker 1: INTRODUCED NODE 5 with 6 open transitions                 I@092206.984
Worker 2: CLOSING NODE 5                                            I@092207.632
Worker 2: Step 5, level 0: collecting 6 enabled transition(s)       I@092207.726
Worker 2: INTRODUCED NODE 6 with 6 open transitions                 I@092207.837
Worker 4: CLOSING NODE 6                                            I@092208.517
Worker 4: Step 6, level 0: collecting 6 enabled transition(s)       I@092208.671
Worker 4: INTRODUCED NODE 7 with 6 open transitions                 I@092208.807
Worker 4: CLOSING NODE 7                                            I@092209.673
Worker 4: Step 7, level 0: collecting 6 enabled transition(s)       I@092209.831
Worker 4: INTRODUCED NODE 8 with 6 open transitions                 I@092209.949
Worker 4: CLOSING NODE 8                                            I@092211.005
Worker 4: Step 8, level 0: collecting 6 enabled transition(s)       I@092211.229
Worker 4: INTRODUCED NODE 9 with 6 open transitions                 I@092211.389
Worker 3: CLOSING NODE 9                                            I@092212.767
Worker 3: Step 9, level 0: collecting 6 enabled transition(s)       I@092213.030
Worker 3: INTRODUCED NODE 10 with 6 open transitions                I@092213.200
Worker 3: CLOSING NODE 10                                           I@092214.921
Worker 3: Step 10, level 0: collecting 6 enabled transition(s)      I@092215.244
Worker 3: INTRODUCED NODE 11 with 6 open transitions                I@092215.449
Worker 2: CLOSING NODE 11                                           I@092217.508
Worker 2: Step 11, level 0: collecting 6 enabled transition(s)      I@092217.928
Worker 2: INTRODUCED NODE 12 with 6 open transitions                I@092218.185
Worker 3: CLOSING NODE 12                                           I@092220.828
Worker 3: Step 12, level 0: collecting 6 enabled transition(s)      I@092221.414
Worker 3: INTRODUCED NODE 13 with 6 open transitions                I@092221.717
Worker 2: CLOSING NODE 13                                           I@092225.180
Worker 2: Step 13, level 0: collecting 6 enabled transition(s)      I@092225.806
Worker 2: INTRODUCED NODE 14 with 6 open transitions                I@092226.094
Worker 2: CLOSING NODE 14                                           I@092229.739
Worker 2: Step 14, level 0: collecting 6 enabled transition(s)      I@092230.565
Worker 2: INTRODUCED NODE 15 with 6 open transitions                I@092231.004
Worker 2: CLOSING NODE 15                                           I@092238.706
Worker 2: Step 15, level 0: collecting 6 enabled transition(s)      I@092239.757
Worker 2: INTRODUCED NODE 16 with 6 open transitions                I@092240.359
Worker 2: CLOSING NODE 16                                           I@092248.209
Worker 2: Step 16, level 0: collecting 6 enabled transition(s)      I@092249.615
Worker 2: INTRODUCED NODE 17 with 6 open transitions                I@092250.212
Worker 4: CLOSING NODE 17                                           I@092259.370
Worker 4: Step 17, level 0: collecting 6 enabled transition(s)      I@092300.876
Worker 4: INTRODUCED NODE 18 with 6 open transitions                I@092301.584
Worker 4: CLOSING NODE 18                                           I@092517.301
Worker 4: Step 18, level 0: collecting 6 enabled transition(s)      I@092518.146
Worker 4: INTRODUCED NODE 19 with 6 open transitions                I@092518.508
Worker 1: CLOSING NODE 19                                           I@092524.941
Worker 1: Step 19, level 0: collecting 6 enabled transition(s)      I@092526.031
Worker 1: INTRODUCED NODE 20 with 6 open transitions                I@092526.568
Worker 1: CLOSING NODE 20                                           I@092534.792
Worker 1: Step 20, level 0: collecting 6 enabled transition(s)      I@092536.694
Worker 1: INTRODUCED NODE 21 with 6 open transitions                I@092537.685
Worker 2: CLOSING NODE 21                                           I@092553.361
Worker 2: Step 21, level 0: collecting 6 enabled transition(s)      I@092555.466
Worker 2: INTRODUCED NODE 22 with 6 open transitions                I@092556.877
Shutdown hook activated. Interrupting the workers and joining them for 5000 ms. E@092819.106
bin/apalache-mc: line 32: 27334 Killed                  java $JVM_ARGS -jar "$JAR" "$@"

real	6m28,444s
user	19m46,938s
sys	0m10,676s


