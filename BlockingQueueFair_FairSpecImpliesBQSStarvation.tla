-------------------------- MODULE BlockingQueueFair_FairSpecImpliesBQSStarvation --------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_1

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_1

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_2

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_2

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_3

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_3

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_4

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_4

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_4_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_4_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_5

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_5

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_6

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_6

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_7

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_7

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_8

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_8

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_8_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_8_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_9

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_9

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_9_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_9_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_a

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_a

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_a_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_a_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_b

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_b

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_b_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_b_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_c

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_c

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_d

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_d

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_e

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_e

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_e_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_e_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_f

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_f

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_f_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_f_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_g

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_g

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_g_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_g_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_h

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_h

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_h_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_h_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_i

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_i

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_j

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_j

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_k

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_k

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_k_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_k_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_l

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_l

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_l_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_l_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_m

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_m

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_n

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_n

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_n_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_n_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_o

VARIABLE
  (*
    @type: Bool;
  *)
  __saved___temporal_t_o

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_o_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_o_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __FairSpecImpliesBQSStarvation_init

VARIABLE
  (*
    @type: Seq(Str);
  *)
  __saved_waitSeqC

VARIABLE
  (*
    @type: Seq(Str);
  *)
  __saved_waitSeqP

VARIABLE
  (*
    @type: Seq(Str);
  *)
  __saved_buffer

VARIABLE
  (*
    @type: Bool;
  *)
  __InLoop

VARIABLE
  (*
    @type: Seq(Str);
  *)
  waitSeqC

VARIABLE
  (*
    @type: Seq(Str);
  *)
  waitSeqP

VARIABLE
  (*
    @type: Seq(Str);
  *)
  buffer

CONSTANT
  (*
    @type: Set(Str);
  *)
  Producers

CONSTANT
  (*
    @type: Set(Str);
  *)
  Consumers

CONSTANT
  (*
    @type: Int;
  *)
  BufCapacity

(*
  @type: (() => Bool);
*)
ASSUME(Producers /= {}
  /\ Consumers /= {}
  /\ Producers \intersect Consumers = {}
  /\ Consumers \intersect Producers = {}
  /\ BufCapacity \in Nat \ {0})

(*
  @type: (() => Bool);
*)
Init ==
  buffer = <<>>
    /\ waitSeqC = <<>>
    /\ waitSeqP = <<>>
    /\ __InLoop = FALSE
    /\ __saved_waitSeqC = waitSeqC
    /\ __saved_waitSeqP = waitSeqP
    /\ __saved_buffer = buffer
    /\ __temporal_t_1 \in BOOLEAN
    /\ __saved___temporal_t_1 = __temporal_t_1
    /\ __temporal_t_2 \in BOOLEAN
    /\ __saved___temporal_t_2 = __temporal_t_2
    /\ __temporal_t_3 \in BOOLEAN
    /\ __saved___temporal_t_3 = __temporal_t_3
    /\ __temporal_t_4 \in BOOLEAN
    /\ __saved___temporal_t_4 = __temporal_t_4
    /\ __temporal_t_4_unroll = TRUE
    /\ __temporal_t_4_unroll_prev = TRUE
    /\ __temporal_t_3
      = (buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>
        /\ __temporal_t_4)
    /\ __temporal_t_5 \in BOOLEAN
    /\ __saved___temporal_t_5 = __temporal_t_5
    /\ __temporal_t_6 \in BOOLEAN
    /\ __saved___temporal_t_6 = __temporal_t_6
    /\ __temporal_t_7 \in BOOLEAN
    /\ __saved___temporal_t_7 = __temporal_t_7
    /\ __temporal_t_8 \in BOOLEAN
    /\ __saved___temporal_t_8 = __temporal_t_8
    /\ __temporal_t_9 \in BOOLEAN
    /\ __saved___temporal_t_9 = __temporal_t_9
    /\ __temporal_t_9_unroll = FALSE
    /\ __temporal_t_9_unroll_prev = FALSE
    /\ __temporal_t_8_unroll = TRUE
    /\ __temporal_t_8_unroll_prev = TRUE
    /\ __temporal_t_a \in BOOLEAN
    /\ __saved___temporal_t_a = __temporal_t_a
    /\ __temporal_t_b \in BOOLEAN
    /\ __saved___temporal_t_b = __temporal_t_b
    /\ __temporal_t_b_unroll = FALSE
    /\ __temporal_t_b_unroll_prev = FALSE
    /\ __temporal_t_a_unroll = TRUE
    /\ __temporal_t_a_unroll_prev = TRUE
    /\ __temporal_t_7 = (__temporal_t_8 \/ __temporal_t_a)
    /\ __temporal_t_c \in BOOLEAN
    /\ __saved___temporal_t_c = __temporal_t_c
    /\ __temporal_t_d \in BOOLEAN
    /\ __saved___temporal_t_d = __temporal_t_d
    /\ __temporal_t_e \in BOOLEAN
    /\ __saved___temporal_t_e = __temporal_t_e
    /\ __temporal_t_f \in BOOLEAN
    /\ __saved___temporal_t_f = __temporal_t_f
    /\ __temporal_t_f_unroll = FALSE
    /\ __temporal_t_f_unroll_prev = FALSE
    /\ __temporal_t_e_unroll = TRUE
    /\ __temporal_t_e_unroll_prev = TRUE
    /\ __temporal_t_g \in BOOLEAN
    /\ __saved___temporal_t_g = __temporal_t_g
    /\ __temporal_t_h \in BOOLEAN
    /\ __saved___temporal_t_h = __temporal_t_h
    /\ __temporal_t_h_unroll = FALSE
    /\ __temporal_t_h_unroll_prev = FALSE
    /\ __temporal_t_g_unroll = TRUE
    /\ __temporal_t_g_unroll_prev = TRUE
    /\ __temporal_t_d = (__temporal_t_e \/ __temporal_t_g)
    /\ __temporal_t_c = (\A p19 \in Producers: __temporal_t_d)
    /\ __temporal_t_6 = (__temporal_t_7 /\ __temporal_t_c)
    /\ __temporal_t_5 = (\A c \in Consumers: __temporal_t_6)
    /\ __temporal_t_2 = (__temporal_t_3 /\ __temporal_t_5)
    /\ __temporal_t_i \in BOOLEAN
    /\ __saved___temporal_t_i = __temporal_t_i
    /\ __temporal_t_j \in BOOLEAN
    /\ __saved___temporal_t_j = __temporal_t_j
    /\ __temporal_t_k \in BOOLEAN
    /\ __saved___temporal_t_k = __temporal_t_k
    /\ __temporal_t_l \in BOOLEAN
    /\ __saved___temporal_t_l = __temporal_t_l
    /\ __temporal_t_l_unroll = FALSE
    /\ __temporal_t_l_unroll_prev = FALSE
    /\ __temporal_t_k_unroll = TRUE
    /\ __temporal_t_k_unroll_prev = TRUE
    /\ __temporal_t_j = (\A p20 \in Producers: __temporal_t_k)
    /\ __temporal_t_m \in BOOLEAN
    /\ __saved___temporal_t_m = __temporal_t_m
    /\ __temporal_t_n \in BOOLEAN
    /\ __saved___temporal_t_n = __temporal_t_n
    /\ __temporal_t_o \in BOOLEAN
    /\ __saved___temporal_t_o = __temporal_t_o
    /\ __temporal_t_o_unroll = FALSE
    /\ __temporal_t_o_unroll_prev = FALSE
    /\ __temporal_t_n_unroll = TRUE
    /\ __temporal_t_n_unroll_prev = TRUE
    /\ __temporal_t_m = (\A c19 \in Consumers: __temporal_t_n)
    /\ __temporal_t_i = (__temporal_t_j /\ __temporal_t_m)
    /\ __temporal_t_1 = (__temporal_t_2 => __temporal_t_i)
    /\ __FairSpecImpliesBQSStarvation_init = __temporal_t_1

(*
  @type: (() => Bool);
*)
Next ==
  ((\E p1 \in Producers:
        p1
            \notin {
              [ x221 \in 1 .. Len(waitSeqP) |-> waitSeqP[x221] ][__x115]:
                __x115 \in
                  DOMAIN ([ x222 \in 1 .. Len(waitSeqP) |-> waitSeqP[x222] ])
            }
          /\ ((Len(buffer) < BufCapacity
              /\ buffer' = Append(buffer, p1)
              /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
              /\ waitSeqP' = waitSeqP)
            \/ (Len(buffer) = BufCapacity
              /\ waitSeqP' = Append(waitSeqP, p1)
              /\ buffer' = buffer
              /\ waitSeqC' = waitSeqC)))
      \/ (\E c1 \in Consumers:
        c1
            \notin {
              [ x223 \in 1 .. Len(waitSeqC) |-> waitSeqC[x223] ][__x116]:
                __x116 \in
                  DOMAIN ([ x224 \in 1 .. Len(waitSeqC) |-> waitSeqC[x224] ])
            }
          /\ ((buffer /= <<>>
              /\ buffer' = Tail(buffer)
              /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
              /\ waitSeqC' = waitSeqC)
            \/ (buffer = <<>>
              /\ waitSeqC' = Append(waitSeqC, c1)
              /\ buffer' = buffer
              /\ waitSeqP' = waitSeqP))))
    /\ __InLoop' \in BOOLEAN
    /\ (__InLoop => __InLoop')
    /\ (IF __InLoop = __InLoop'
    THEN UNCHANGED (<<__saved_waitSeqC, __saved_waitSeqP, __saved_buffer>>)
    ELSE __saved_waitSeqC' = waitSeqC
      /\ __saved_waitSeqP' = waitSeqP
      /\ __saved_buffer' = buffer)
    /\ __temporal_t_1' \in BOOLEAN
    /\ __saved___temporal_t_1'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_1 ELSE __temporal_t_1)
    /\ __temporal_t_2' \in BOOLEAN
    /\ __saved___temporal_t_2'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_2 ELSE __temporal_t_2)
    /\ __temporal_t_3' \in BOOLEAN
    /\ __saved___temporal_t_3'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_3 ELSE __temporal_t_3)
    /\ __temporal_t_4' \in BOOLEAN
    /\ __saved___temporal_t_4'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_4 ELSE __temporal_t_4)
    /\ __temporal_t_4_unroll' \in BOOLEAN
    /\ (__temporal_t_4
      <=> ((\E p18 \in Producers:
            p18
                \notin {
                  [ x1869 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1869] ][
                    __x935
                  ]:
                    __x935 \in
                      DOMAIN ([
                        x1870 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1870]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p18)
                  /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                    \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
                  /\ waitSeqP' = waitSeqP)
                \/ (Len(buffer) = BufCapacity
                  /\ waitSeqP' = Append(waitSeqP, p18)
                  /\ buffer' = buffer
                  /\ waitSeqC' = waitSeqC)))
          \/ (\E c17 \in Consumers:
            c17
                \notin {
                  [ x1871 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1871] ][
                    __x936
                  ]:
                    __x936 \in
                      DOMAIN ([
                        x1872 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1872]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                    \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
                  /\ waitSeqC' = waitSeqC)
                \/ (buffer = <<>>
                  /\ waitSeqC' = Append(waitSeqC, c17)
                  /\ buffer' = buffer
                  /\ waitSeqP' = waitSeqP)))
          \/ <<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>)
        /\ __temporal_t_4')
    /\ (__temporal_t_4_unroll
      <=> __temporal_t_4_unroll_prev
        /\ (~__InLoop'
          \/ (\E p18 \in Producers:
            p18
                \notin {
                  [ x1869 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1869] ][
                    __x935
                  ]:
                    __x935 \in
                      DOMAIN ([
                        x1870 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1870]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p18)
                  /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                    \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
                  /\ waitSeqP' = waitSeqP)
                \/ (Len(buffer) = BufCapacity
                  /\ waitSeqP' = Append(waitSeqP, p18)
                  /\ buffer' = buffer
                  /\ waitSeqC' = waitSeqC)))
          \/ (\E c17 \in Consumers:
            c17
                \notin {
                  [ x1871 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1871] ][
                    __x936
                  ]:
                    __x936 \in
                      DOMAIN ([
                        x1872 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1872]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                    \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
                  /\ waitSeqC' = waitSeqC)
                \/ (buffer = <<>>
                  /\ waitSeqC' = Append(waitSeqC, c17)
                  /\ buffer' = buffer
                  /\ waitSeqP' = waitSeqP)))
          \/ <<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>))
    /\ __temporal_t_4_unroll_prev' = __temporal_t_4_unroll
    /\ __temporal_t_3'
      = (buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>
        /\ __temporal_t_4)
    /\ __temporal_t_5' \in BOOLEAN
    /\ __saved___temporal_t_5'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_5 ELSE __temporal_t_5)
    /\ __temporal_t_6' \in BOOLEAN
    /\ __saved___temporal_t_6'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_6 ELSE __temporal_t_6)
    /\ __temporal_t_7' \in BOOLEAN
    /\ __saved___temporal_t_7'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_7 ELSE __temporal_t_7)
    /\ __temporal_t_8' \in BOOLEAN
    /\ __saved___temporal_t_8'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_8 ELSE __temporal_t_8)
    /\ __temporal_t_9' \in BOOLEAN
    /\ __saved___temporal_t_9'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_9 ELSE __temporal_t_9)
    /\ __temporal_t_9_unroll' \in BOOLEAN
    /\ (__temporal_t_9
      <=> ~((~(\E c \in Consumers: c
              \in {
                [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][__x937]:
                  __x937 \in
                    DOMAIN ([
                      x1874 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1874]
                    ])
              })
            /\ ~(buffer = <<>>)
            /\ waitSeqP = <<>>
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>))
          \/ (~(\E c \in Consumers: c
              \in {
                [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][__x937]:
                  __x937 \in
                    DOMAIN ([
                      x1874 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1874]
                    ])
              })
            /\ ~(buffer = <<>>)
            /\ ~(waitSeqP = <<>>)
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>))
          \/ (~(\E c \in Consumers: c
              \in {
                [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][__x937]:
                  __x937 \in
                    DOMAIN ([
                      x1874 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1874]
                    ])
              })
            /\ buffer = <<>>
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>)))
        \/ __temporal_t_9')
    /\ (__temporal_t_9_unroll
      <=> __temporal_t_9_unroll_prev
        \/ (__InLoop'
          /\ ~((~(\E c \in Consumers: c
                \in {
                  [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][
                    __x937
                  ]:
                    __x937 \in
                      DOMAIN ([
                        x1874 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1874]
                      ])
                })
              /\ ~(buffer = <<>>)
              /\ waitSeqP = <<>>
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>))
            \/ (~(\E c \in Consumers: c
                \in {
                  [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][
                    __x937
                  ]:
                    __x937 \in
                      DOMAIN ([
                        x1874 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1874]
                      ])
                })
              /\ ~(buffer = <<>>)
              /\ ~(waitSeqP = <<>>)
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>))
            \/ (~(\E c \in Consumers: c
                \in {
                  [ x1873 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1873] ][
                    __x937
                  ]:
                    __x937 \in
                      DOMAIN ([
                        x1874 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1874]
                      ])
                })
              /\ buffer = <<>>
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>)))))
    /\ __temporal_t_9_unroll_prev' = __temporal_t_9_unroll
    /\ __temporal_t_8_unroll' \in BOOLEAN
    /\ (__temporal_t_8 <=> __temporal_t_9 /\ __temporal_t_8')
    /\ (__temporal_t_8_unroll
      <=> __temporal_t_8_unroll_prev /\ (~__InLoop' \/ __temporal_t_9))
    /\ __temporal_t_8_unroll_prev' = __temporal_t_8_unroll
    /\ __temporal_t_a' \in BOOLEAN
    /\ __saved___temporal_t_a'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_a ELSE __temporal_t_a)
    /\ __temporal_t_b' \in BOOLEAN
    /\ __saved___temporal_t_b'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_b ELSE __temporal_t_b)
    /\ __temporal_t_b_unroll' \in BOOLEAN
    /\ (__temporal_t_b
      <=> (\E c \in Consumers: c
            \notin {
              [ x1875 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1875] ][__x938]:
                __x938 \in
                  DOMAIN ([ x1876 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1876] ])
            }
          /\ ((buffer /= <<>>
              /\ buffer' = Tail(buffer)
              /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
              /\ waitSeqC' = waitSeqC)
            \/ (buffer = <<>>
              /\ waitSeqC' = Append(waitSeqC, c)
              /\ buffer' = buffer
              /\ waitSeqP' = waitSeqP))
          /\ ~(<<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>))
        \/ __temporal_t_b')
    /\ (__temporal_t_b_unroll
      <=> __temporal_t_b_unroll_prev
        \/ (__InLoop'
          /\ \E c \in Consumers: c
            \notin {
              [ x1875 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1875] ][__x938]:
                __x938 \in
                  DOMAIN ([ x1876 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1876] ])
            }
          /\ ((buffer /= <<>>
              /\ buffer' = Tail(buffer)
              /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
              /\ waitSeqC' = waitSeqC)
            \/ (buffer = <<>>
              /\ waitSeqC' = Append(waitSeqC, c)
              /\ buffer' = buffer
              /\ waitSeqP' = waitSeqP))
          /\ ~(<<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>)))
    /\ __temporal_t_b_unroll_prev' = __temporal_t_b_unroll
    /\ __temporal_t_a_unroll' \in BOOLEAN
    /\ (__temporal_t_a <=> __temporal_t_b /\ __temporal_t_a')
    /\ (__temporal_t_a_unroll
      <=> __temporal_t_a_unroll_prev /\ (~__InLoop' \/ __temporal_t_b))
    /\ __temporal_t_a_unroll_prev' = __temporal_t_a_unroll
    /\ __temporal_t_7' = (__temporal_t_8 \/ __temporal_t_a)
    /\ __temporal_t_c' \in BOOLEAN
    /\ __saved___temporal_t_c'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_c ELSE __temporal_t_c)
    /\ __temporal_t_d' \in BOOLEAN
    /\ __saved___temporal_t_d'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_d ELSE __temporal_t_d)
    /\ __temporal_t_e' \in BOOLEAN
    /\ __saved___temporal_t_e'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_e ELSE __temporal_t_e)
    /\ __temporal_t_f' \in BOOLEAN
    /\ __saved___temporal_t_f'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_f ELSE __temporal_t_f)
    /\ __temporal_t_f_unroll' \in BOOLEAN
    /\ (__temporal_t_f
      <=> ~((~(\E p19 \in Producers: p19
              \in {
                [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][__x939]:
                  __x939 \in
                    DOMAIN ([
                      x1878 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1878]
                    ])
              })
            /\ Len(buffer) < BufCapacity
            /\ waitSeqC = <<>>
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>))
          \/ (~(\E p19 \in Producers: p19
              \in {
                [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][__x939]:
                  __x939 \in
                    DOMAIN ([
                      x1878 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1878]
                    ])
              })
            /\ Len(buffer) < BufCapacity
            /\ ~(waitSeqC = <<>>)
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>))
          \/ (~(\E p19 \in Producers: p19
              \in {
                [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][__x939]:
                  __x939 \in
                    DOMAIN ([
                      x1878 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1878]
                    ])
              })
            /\ Len(buffer) = BufCapacity
            /\ ~(<<buffer, waitSeqC, waitSeqP>>'
              = <<buffer, waitSeqC, waitSeqP>>)))
        \/ __temporal_t_f')
    /\ (__temporal_t_f_unroll
      <=> __temporal_t_f_unroll_prev
        \/ (__InLoop'
          /\ ~((~(\E p19 \in Producers: p19
                \in {
                  [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][
                    __x939
                  ]:
                    __x939 \in
                      DOMAIN ([
                        x1878 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1878]
                      ])
                })
              /\ Len(buffer) < BufCapacity
              /\ waitSeqC = <<>>
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>))
            \/ (~(\E p19 \in Producers: p19
                \in {
                  [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][
                    __x939
                  ]:
                    __x939 \in
                      DOMAIN ([
                        x1878 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1878]
                      ])
                })
              /\ Len(buffer) < BufCapacity
              /\ ~(waitSeqC = <<>>)
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>))
            \/ (~(\E p19 \in Producers: p19
                \in {
                  [ x1877 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1877] ][
                    __x939
                  ]:
                    __x939 \in
                      DOMAIN ([
                        x1878 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1878]
                      ])
                })
              /\ Len(buffer) = BufCapacity
              /\ ~(<<buffer, waitSeqC, waitSeqP>>'
                = <<buffer, waitSeqC, waitSeqP>>)))))
    /\ __temporal_t_f_unroll_prev' = __temporal_t_f_unroll
    /\ __temporal_t_e_unroll' \in BOOLEAN
    /\ (__temporal_t_e <=> __temporal_t_f /\ __temporal_t_e')
    /\ (__temporal_t_e_unroll
      <=> __temporal_t_e_unroll_prev /\ (~__InLoop' \/ __temporal_t_f))
    /\ __temporal_t_e_unroll_prev' = __temporal_t_e_unroll
    /\ __temporal_t_g' \in BOOLEAN
    /\ __saved___temporal_t_g'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_g ELSE __temporal_t_g)
    /\ __temporal_t_h' \in BOOLEAN
    /\ __saved___temporal_t_h'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_h ELSE __temporal_t_h)
    /\ __temporal_t_h_unroll' \in BOOLEAN
    /\ (__temporal_t_h
      <=> (\E p19 \in Producers: p19
            \notin {
              [ x1879 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1879] ][__x940]:
                __x940 \in
                  DOMAIN ([ x1880 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1880] ])
            }
          /\ ((Len(buffer) < BufCapacity
              /\ buffer' = Append(buffer, p19)
              /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
              /\ waitSeqP' = waitSeqP)
            \/ (Len(buffer) = BufCapacity
              /\ waitSeqP' = Append(waitSeqP, p19)
              /\ buffer' = buffer
              /\ waitSeqC' = waitSeqC))
          /\ ~(<<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>))
        \/ __temporal_t_h')
    /\ (__temporal_t_h_unroll
      <=> __temporal_t_h_unroll_prev
        \/ (__InLoop'
          /\ \E p19 \in Producers: p19
            \notin {
              [ x1879 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1879] ][__x940]:
                __x940 \in
                  DOMAIN ([ x1880 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1880] ])
            }
          /\ ((Len(buffer) < BufCapacity
              /\ buffer' = Append(buffer, p19)
              /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
              /\ waitSeqP' = waitSeqP)
            \/ (Len(buffer) = BufCapacity
              /\ waitSeqP' = Append(waitSeqP, p19)
              /\ buffer' = buffer
              /\ waitSeqC' = waitSeqC))
          /\ ~(<<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>)))
    /\ __temporal_t_h_unroll_prev' = __temporal_t_h_unroll
    /\ __temporal_t_g_unroll' \in BOOLEAN
    /\ (__temporal_t_g <=> __temporal_t_h /\ __temporal_t_g')
    /\ (__temporal_t_g_unroll
      <=> __temporal_t_g_unroll_prev /\ (~__InLoop' \/ __temporal_t_h))
    /\ __temporal_t_g_unroll_prev' = __temporal_t_g_unroll
    /\ __temporal_t_d' = (__temporal_t_e \/ __temporal_t_g)
    /\ __temporal_t_c' = (\A p19 \in Producers: __temporal_t_d)
    /\ __temporal_t_6' = (__temporal_t_7 /\ __temporal_t_c)
    /\ __temporal_t_5' = (\A c \in Consumers: __temporal_t_6)
    /\ __temporal_t_2' = (__temporal_t_3 /\ __temporal_t_5)
    /\ __temporal_t_i' \in BOOLEAN
    /\ __saved___temporal_t_i'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_i ELSE __temporal_t_i)
    /\ __temporal_t_j' \in BOOLEAN
    /\ __saved___temporal_t_j'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_j ELSE __temporal_t_j)
    /\ __temporal_t_k' \in BOOLEAN
    /\ __saved___temporal_t_k'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_k ELSE __temporal_t_k)
    /\ __temporal_t_l' \in BOOLEAN
    /\ __saved___temporal_t_l'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_l ELSE __temporal_t_l)
    /\ __temporal_t_l_unroll' \in BOOLEAN
    /\ (__temporal_t_l
      <=> (\E p20 \in Producers: p20
            \notin {
              [ x1881 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1881] ][__x941]:
                __x941 \in
                  DOMAIN ([ x1882 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1882] ])
            }
              \union {
                [ x1883 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1883] ][__x942]:
                  __x942 \in
                    DOMAIN ([
                      x1884 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1884]
                    ])
              }
          /\ ((Len(buffer) < BufCapacity
              /\ buffer' = Append(buffer, p20)
              /\ (IF ({
                [ x1885 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1885] ][__x943]:
                  __x943 \in
                    DOMAIN ([
                      x1886 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1886]
                    ])
              }
                \union {
                  [ x1887 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1887] ][
                    __x944
                  ]:
                    __x944 \in
                      DOMAIN ([
                        x1888 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1888]
                      ])
                })
                \intersect Consumers
                /= {}
              THEN \E t43 \in ({
                [ x1889 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1889] ][__x945]:
                  __x945 \in
                    DOMAIN ([
                      x1890 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1890]
                    ])
              }
                \union {
                  [ x1891 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1891] ][
                    __x946
                  ]:
                    __x946 \in
                      DOMAIN ([
                        x1892 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1892]
                      ])
                })
                \intersect Consumers:
                ({
                  [ x1893 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1893] ][
                    __x947
                  ]:
                    __x947 \in
                      DOMAIN ([
                        x1894 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1894]
                      ])
                }
                  \union {
                    [ x1895 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1895] ][
                      __x948
                    ]:
                      __x948 \in
                        DOMAIN ([
                          x1896 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1896]
                        ])
                  })'
                  = ({
                    [ x1897 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1897] ][
                      __x949
                    ]:
                      __x949 \in
                        DOMAIN ([
                          x1898 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1898]
                        ])
                  }
                    \union {
                      [ x1899 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1899] ][
                        __x950
                      ]:
                        __x950 \in
                          DOMAIN ([
                            x1900 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1900]
                          ])
                    })
                    \ {t43}
              ELSE ({
                [ x1901 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1901] ][__x951]:
                  __x951 \in
                    DOMAIN ([
                      x1902 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1902]
                    ])
              }
                \union {
                  [ x1903 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1903] ][
                    __x952
                  ]:
                    __x952 \in
                      DOMAIN ([
                        x1904 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1904]
                      ])
                })'
                = {
                  [ x1905 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1905] ][
                    __x953
                  ]:
                    __x953 \in
                      DOMAIN ([
                        x1906 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1906]
                      ])
                }
                  \union {
                    [ x1907 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1907] ][
                      __x954
                    ]:
                      __x954 \in
                        DOMAIN ([
                          x1908 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1908]
                        ])
                  }))
            \/ (Len(buffer) = BufCapacity
              /\ ({
                [ x1909 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1909] ][__x955]:
                  __x955 \in
                    DOMAIN ([
                      x1910 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1910]
                    ])
              }
                \union {
                  [ x1911 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1911] ][
                    __x956
                  ]:
                    __x956 \in
                      DOMAIN ([
                        x1912 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1912]
                      ])
                })'
                = ({
                  [ x1913 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1913] ][
                    __x957
                  ]:
                    __x957 \in
                      DOMAIN ([
                        x1914 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1914]
                      ])
                }
                  \union {
                    [ x1915 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1915] ][
                      __x958
                    ]:
                      __x958 \in
                        DOMAIN ([
                          x1916 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1916]
                        ])
                  })
                  \union {p20}
              /\ buffer' = buffer))
          /\ ~(<<
            buffer, ({
              [ x1917 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1917] ][__x959]:
                __x959 \in
                  DOMAIN ([ x1918 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1918] ])
            }
              \union {
                [ x1919 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1919] ][__x960]:
                  __x960 \in
                    DOMAIN ([
                      x1920 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1920]
                    ])
              })
          >>'
            = <<
              buffer, ({
                [ x1921 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1921] ][__x961]:
                  __x961 \in
                    DOMAIN ([
                      x1922 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1922]
                    ])
              }
                \union {
                  [ x1923 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1923] ][
                    __x962
                  ]:
                    __x962 \in
                      DOMAIN ([
                        x1924 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1924]
                      ])
                })
            >>))
        \/ __temporal_t_l')
    /\ (__temporal_t_l_unroll
      <=> __temporal_t_l_unroll_prev
        \/ (__InLoop'
          /\ \E p20 \in Producers: p20
            \notin {
              [ x1881 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1881] ][__x941]:
                __x941 \in
                  DOMAIN ([ x1882 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1882] ])
            }
              \union {
                [ x1883 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1883] ][__x942]:
                  __x942 \in
                    DOMAIN ([
                      x1884 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1884]
                    ])
              }
          /\ ((Len(buffer) < BufCapacity
              /\ buffer' = Append(buffer, p20)
              /\ (IF ({
                [ x1885 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1885] ][__x943]:
                  __x943 \in
                    DOMAIN ([
                      x1886 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1886]
                    ])
              }
                \union {
                  [ x1887 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1887] ][
                    __x944
                  ]:
                    __x944 \in
                      DOMAIN ([
                        x1888 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1888]
                      ])
                })
                \intersect Consumers
                /= {}
              THEN \E t43 \in ({
                [ x1889 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1889] ][__x945]:
                  __x945 \in
                    DOMAIN ([
                      x1890 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1890]
                    ])
              }
                \union {
                  [ x1891 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1891] ][
                    __x946
                  ]:
                    __x946 \in
                      DOMAIN ([
                        x1892 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1892]
                      ])
                })
                \intersect Consumers:
                ({
                  [ x1893 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1893] ][
                    __x947
                  ]:
                    __x947 \in
                      DOMAIN ([
                        x1894 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1894]
                      ])
                }
                  \union {
                    [ x1895 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1895] ][
                      __x948
                    ]:
                      __x948 \in
                        DOMAIN ([
                          x1896 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1896]
                        ])
                  })'
                  = ({
                    [ x1897 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1897] ][
                      __x949
                    ]:
                      __x949 \in
                        DOMAIN ([
                          x1898 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1898]
                        ])
                  }
                    \union {
                      [ x1899 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1899] ][
                        __x950
                      ]:
                        __x950 \in
                          DOMAIN ([
                            x1900 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1900]
                          ])
                    })
                    \ {t43}
              ELSE ({
                [ x1901 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1901] ][__x951]:
                  __x951 \in
                    DOMAIN ([
                      x1902 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1902]
                    ])
              }
                \union {
                  [ x1903 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1903] ][
                    __x952
                  ]:
                    __x952 \in
                      DOMAIN ([
                        x1904 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1904]
                      ])
                })'
                = {
                  [ x1905 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1905] ][
                    __x953
                  ]:
                    __x953 \in
                      DOMAIN ([
                        x1906 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1906]
                      ])
                }
                  \union {
                    [ x1907 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1907] ][
                      __x954
                    ]:
                      __x954 \in
                        DOMAIN ([
                          x1908 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1908]
                        ])
                  }))
            \/ (Len(buffer) = BufCapacity
              /\ ({
                [ x1909 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1909] ][__x955]:
                  __x955 \in
                    DOMAIN ([
                      x1910 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1910]
                    ])
              }
                \union {
                  [ x1911 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1911] ][
                    __x956
                  ]:
                    __x956 \in
                      DOMAIN ([
                        x1912 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1912]
                      ])
                })'
                = ({
                  [ x1913 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1913] ][
                    __x957
                  ]:
                    __x957 \in
                      DOMAIN ([
                        x1914 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1914]
                      ])
                }
                  \union {
                    [ x1915 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1915] ][
                      __x958
                    ]:
                      __x958 \in
                        DOMAIN ([
                          x1916 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1916]
                        ])
                  })
                  \union {p20}
              /\ buffer' = buffer))
          /\ ~(<<
            buffer, ({
              [ x1917 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1917] ][__x959]:
                __x959 \in
                  DOMAIN ([ x1918 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1918] ])
            }
              \union {
                [ x1919 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1919] ][__x960]:
                  __x960 \in
                    DOMAIN ([
                      x1920 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1920]
                    ])
              })
          >>'
            = <<
              buffer, ({
                [ x1921 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1921] ][__x961]:
                  __x961 \in
                    DOMAIN ([
                      x1922 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1922]
                    ])
              }
                \union {
                  [ x1923 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1923] ][
                    __x962
                  ]:
                    __x962 \in
                      DOMAIN ([
                        x1924 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1924]
                      ])
                })
            >>)))
    /\ __temporal_t_l_unroll_prev' = __temporal_t_l_unroll
    /\ __temporal_t_k_unroll' \in BOOLEAN
    /\ (__temporal_t_k <=> __temporal_t_l /\ __temporal_t_k')
    /\ (__temporal_t_k_unroll
      <=> __temporal_t_k_unroll_prev /\ (~__InLoop' \/ __temporal_t_l))
    /\ __temporal_t_k_unroll_prev' = __temporal_t_k_unroll
    /\ __temporal_t_j' = (\A p20 \in Producers: __temporal_t_k)
    /\ __temporal_t_m' \in BOOLEAN
    /\ __saved___temporal_t_m'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_m ELSE __temporal_t_m)
    /\ __temporal_t_n' \in BOOLEAN
    /\ __saved___temporal_t_n'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_n ELSE __temporal_t_n)
    /\ __temporal_t_o' \in BOOLEAN
    /\ __saved___temporal_t_o'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_o ELSE __temporal_t_o)
    /\ __temporal_t_o_unroll' \in BOOLEAN
    /\ (__temporal_t_o
      <=> (\E c19 \in Consumers: c19
            \notin {
              [ x1925 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1925] ][__x963]:
                __x963 \in
                  DOMAIN ([ x1926 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1926] ])
            }
              \union {
                [ x1927 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1927] ][__x964]:
                  __x964 \in
                    DOMAIN ([
                      x1928 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1928]
                    ])
              }
          /\ ((buffer /= <<>>
              /\ buffer' = Tail(buffer)
              /\ (IF ({
                [ x1929 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1929] ][__x965]:
                  __x965 \in
                    DOMAIN ([
                      x1930 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1930]
                    ])
              }
                \union {
                  [ x1931 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1931] ][
                    __x966
                  ]:
                    __x966 \in
                      DOMAIN ([
                        x1932 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1932]
                      ])
                })
                \intersect Producers
                /= {}
              THEN \E t44 \in ({
                [ x1933 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1933] ][__x967]:
                  __x967 \in
                    DOMAIN ([
                      x1934 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1934]
                    ])
              }
                \union {
                  [ x1935 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1935] ][
                    __x968
                  ]:
                    __x968 \in
                      DOMAIN ([
                        x1936 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1936]
                      ])
                })
                \intersect Producers:
                ({
                  [ x1937 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1937] ][
                    __x969
                  ]:
                    __x969 \in
                      DOMAIN ([
                        x1938 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1938]
                      ])
                }
                  \union {
                    [ x1939 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1939] ][
                      __x970
                    ]:
                      __x970 \in
                        DOMAIN ([
                          x1940 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1940]
                        ])
                  })'
                  = ({
                    [ x1941 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1941] ][
                      __x971
                    ]:
                      __x971 \in
                        DOMAIN ([
                          x1942 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1942]
                        ])
                  }
                    \union {
                      [ x1943 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1943] ][
                        __x972
                      ]:
                        __x972 \in
                          DOMAIN ([
                            x1944 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1944]
                          ])
                    })
                    \ {t44}
              ELSE ({
                [ x1945 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1945] ][__x973]:
                  __x973 \in
                    DOMAIN ([
                      x1946 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1946]
                    ])
              }
                \union {
                  [ x1947 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1947] ][
                    __x974
                  ]:
                    __x974 \in
                      DOMAIN ([
                        x1948 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1948]
                      ])
                })'
                = {
                  [ x1949 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1949] ][
                    __x975
                  ]:
                    __x975 \in
                      DOMAIN ([
                        x1950 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1950]
                      ])
                }
                  \union {
                    [ x1951 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1951] ][
                      __x976
                    ]:
                      __x976 \in
                        DOMAIN ([
                          x1952 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1952]
                        ])
                  }))
            \/ (buffer = <<>>
              /\ ({
                [ x1953 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1953] ][__x977]:
                  __x977 \in
                    DOMAIN ([
                      x1954 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1954]
                    ])
              }
                \union {
                  [ x1955 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1955] ][
                    __x978
                  ]:
                    __x978 \in
                      DOMAIN ([
                        x1956 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1956]
                      ])
                })'
                = ({
                  [ x1957 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1957] ][
                    __x979
                  ]:
                    __x979 \in
                      DOMAIN ([
                        x1958 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1958]
                      ])
                }
                  \union {
                    [ x1959 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1959] ][
                      __x980
                    ]:
                      __x980 \in
                        DOMAIN ([
                          x1960 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1960]
                        ])
                  })
                  \union {c19}
              /\ buffer' = buffer))
          /\ ~(<<
            buffer, ({
              [ x1961 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1961] ][__x981]:
                __x981 \in
                  DOMAIN ([ x1962 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1962] ])
            }
              \union {
                [ x1963 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1963] ][__x982]:
                  __x982 \in
                    DOMAIN ([
                      x1964 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1964]
                    ])
              })
          >>'
            = <<
              buffer, ({
                [ x1965 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1965] ][__x983]:
                  __x983 \in
                    DOMAIN ([
                      x1966 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1966]
                    ])
              }
                \union {
                  [ x1967 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1967] ][
                    __x984
                  ]:
                    __x984 \in
                      DOMAIN ([
                        x1968 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1968]
                      ])
                })
            >>))
        \/ __temporal_t_o')
    /\ (__temporal_t_o_unroll
      <=> __temporal_t_o_unroll_prev
        \/ (__InLoop'
          /\ \E c19 \in Consumers: c19
            \notin {
              [ x1925 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1925] ][__x963]:
                __x963 \in
                  DOMAIN ([ x1926 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1926] ])
            }
              \union {
                [ x1927 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1927] ][__x964]:
                  __x964 \in
                    DOMAIN ([
                      x1928 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1928]
                    ])
              }
          /\ ((buffer /= <<>>
              /\ buffer' = Tail(buffer)
              /\ (IF ({
                [ x1929 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1929] ][__x965]:
                  __x965 \in
                    DOMAIN ([
                      x1930 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1930]
                    ])
              }
                \union {
                  [ x1931 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1931] ][
                    __x966
                  ]:
                    __x966 \in
                      DOMAIN ([
                        x1932 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1932]
                      ])
                })
                \intersect Producers
                /= {}
              THEN \E t44 \in ({
                [ x1933 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1933] ][__x967]:
                  __x967 \in
                    DOMAIN ([
                      x1934 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1934]
                    ])
              }
                \union {
                  [ x1935 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1935] ][
                    __x968
                  ]:
                    __x968 \in
                      DOMAIN ([
                        x1936 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1936]
                      ])
                })
                \intersect Producers:
                ({
                  [ x1937 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1937] ][
                    __x969
                  ]:
                    __x969 \in
                      DOMAIN ([
                        x1938 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1938]
                      ])
                }
                  \union {
                    [ x1939 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1939] ][
                      __x970
                    ]:
                      __x970 \in
                        DOMAIN ([
                          x1940 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1940]
                        ])
                  })'
                  = ({
                    [ x1941 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1941] ][
                      __x971
                    ]:
                      __x971 \in
                        DOMAIN ([
                          x1942 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1942]
                        ])
                  }
                    \union {
                      [ x1943 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1943] ][
                        __x972
                      ]:
                        __x972 \in
                          DOMAIN ([
                            x1944 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1944]
                          ])
                    })
                    \ {t44}
              ELSE ({
                [ x1945 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1945] ][__x973]:
                  __x973 \in
                    DOMAIN ([
                      x1946 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1946]
                    ])
              }
                \union {
                  [ x1947 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1947] ][
                    __x974
                  ]:
                    __x974 \in
                      DOMAIN ([
                        x1948 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1948]
                      ])
                })'
                = {
                  [ x1949 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1949] ][
                    __x975
                  ]:
                    __x975 \in
                      DOMAIN ([
                        x1950 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1950]
                      ])
                }
                  \union {
                    [ x1951 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1951] ][
                      __x976
                    ]:
                      __x976 \in
                        DOMAIN ([
                          x1952 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1952]
                        ])
                  }))
            \/ (buffer = <<>>
              /\ ({
                [ x1953 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1953] ][__x977]:
                  __x977 \in
                    DOMAIN ([
                      x1954 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1954]
                    ])
              }
                \union {
                  [ x1955 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1955] ][
                    __x978
                  ]:
                    __x978 \in
                      DOMAIN ([
                        x1956 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1956]
                      ])
                })'
                = ({
                  [ x1957 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1957] ][
                    __x979
                  ]:
                    __x979 \in
                      DOMAIN ([
                        x1958 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1958]
                      ])
                }
                  \union {
                    [ x1959 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1959] ][
                      __x980
                    ]:
                      __x980 \in
                        DOMAIN ([
                          x1960 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1960]
                        ])
                  })
                  \union {c19}
              /\ buffer' = buffer))
          /\ ~(<<
            buffer, ({
              [ x1961 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1961] ][__x981]:
                __x981 \in
                  DOMAIN ([ x1962 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1962] ])
            }
              \union {
                [ x1963 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1963] ][__x982]:
                  __x982 \in
                    DOMAIN ([
                      x1964 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1964]
                    ])
              })
          >>'
            = <<
              buffer, ({
                [ x1965 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1965] ][__x983]:
                  __x983 \in
                    DOMAIN ([
                      x1966 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1966]
                    ])
              }
                \union {
                  [ x1967 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1967] ][
                    __x984
                  ]:
                    __x984 \in
                      DOMAIN ([
                        x1968 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1968]
                      ])
                })
            >>)))
    /\ __temporal_t_o_unroll_prev' = __temporal_t_o_unroll
    /\ __temporal_t_n_unroll' \in BOOLEAN
    /\ (__temporal_t_n <=> __temporal_t_o /\ __temporal_t_n')
    /\ (__temporal_t_n_unroll
      <=> __temporal_t_n_unroll_prev /\ (~__InLoop' \/ __temporal_t_o))
    /\ __temporal_t_n_unroll_prev' = __temporal_t_n_unroll
    /\ __temporal_t_m' = (\A c19 \in Consumers: __temporal_t_n)
    /\ __temporal_t_i' = (__temporal_t_j /\ __temporal_t_m)
    /\ __temporal_t_1' = (__temporal_t_2 => __temporal_t_i)
    /\ UNCHANGED __FairSpecImpliesBQSStarvation_init

(*
  @type: (() => Bool);
*)
__LoopOK ==
  __InLoop
    /\ waitSeqC = __saved_waitSeqC
    /\ waitSeqP = __saved_waitSeqP
    /\ buffer = __saved_buffer
    /\ __temporal_t_1 = __saved___temporal_t_1
    /\ __temporal_t_2 = __saved___temporal_t_2
    /\ __temporal_t_3 = __saved___temporal_t_3
    /\ __temporal_t_4 = __saved___temporal_t_4
    /\ (__temporal_t_4_unroll => __temporal_t_4)
    /\ __temporal_t_4_unroll_prev = __temporal_t_4_unroll
    /\ __temporal_t_5 = __saved___temporal_t_5
    /\ __temporal_t_6 = __saved___temporal_t_6
    /\ __temporal_t_7 = __saved___temporal_t_7
    /\ __temporal_t_8 = __saved___temporal_t_8
    /\ __temporal_t_9 = __saved___temporal_t_9
    /\ (__temporal_t_9 => __temporal_t_9_unroll)
    /\ __temporal_t_9_unroll_prev = __temporal_t_9_unroll
    /\ (__temporal_t_8_unroll => __temporal_t_8)
    /\ __temporal_t_8_unroll_prev = __temporal_t_8_unroll
    /\ __temporal_t_a = __saved___temporal_t_a
    /\ __temporal_t_b = __saved___temporal_t_b
    /\ (__temporal_t_b => __temporal_t_b_unroll)
    /\ __temporal_t_b_unroll_prev = __temporal_t_b_unroll
    /\ (__temporal_t_a_unroll => __temporal_t_a)
    /\ __temporal_t_a_unroll_prev = __temporal_t_a_unroll
    /\ __temporal_t_c = __saved___temporal_t_c
    /\ __temporal_t_d = __saved___temporal_t_d
    /\ __temporal_t_e = __saved___temporal_t_e
    /\ __temporal_t_f = __saved___temporal_t_f
    /\ (__temporal_t_f => __temporal_t_f_unroll)
    /\ __temporal_t_f_unroll_prev = __temporal_t_f_unroll
    /\ (__temporal_t_e_unroll => __temporal_t_e)
    /\ __temporal_t_e_unroll_prev = __temporal_t_e_unroll
    /\ __temporal_t_g = __saved___temporal_t_g
    /\ __temporal_t_h = __saved___temporal_t_h
    /\ (__temporal_t_h => __temporal_t_h_unroll)
    /\ __temporal_t_h_unroll_prev = __temporal_t_h_unroll
    /\ (__temporal_t_g_unroll => __temporal_t_g)
    /\ __temporal_t_g_unroll_prev = __temporal_t_g_unroll
    /\ __temporal_t_i = __saved___temporal_t_i
    /\ __temporal_t_j = __saved___temporal_t_j
    /\ __temporal_t_k = __saved___temporal_t_k
    /\ __temporal_t_l = __saved___temporal_t_l
    /\ (__temporal_t_l => __temporal_t_l_unroll)
    /\ __temporal_t_l_unroll_prev = __temporal_t_l_unroll
    /\ (__temporal_t_k_unroll => __temporal_t_k)
    /\ __temporal_t_k_unroll_prev = __temporal_t_k_unroll
    /\ __temporal_t_m = __saved___temporal_t_m
    /\ __temporal_t_n = __saved___temporal_t_n
    /\ __temporal_t_o = __saved___temporal_t_o
    /\ (__temporal_t_o => __temporal_t_o_unroll)
    /\ __temporal_t_o_unroll_prev = __temporal_t_o_unroll
    /\ (__temporal_t_n_unroll => __temporal_t_n)
    /\ __temporal_t_n_unroll_prev = __temporal_t_n_unroll

(*
  @type: (() => Bool);
*)
FairSpecImpliesBQSStarvation == __LoopOK => __FairSpecImpliesBQSStarvation_init

================================================================================
