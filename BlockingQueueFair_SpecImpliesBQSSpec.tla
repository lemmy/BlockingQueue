-------------------------- MODULE BlockingQueueFair_SpecImpliesBQSSpec --------------------------

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
  __temporal_t_3_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_3_unroll_prev

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
  __temporal_t_5_unroll

VARIABLE
  (*
    @type: Bool;
  *)
  __temporal_t_5_unroll_prev

VARIABLE
  (*
    @type: Bool;
  *)
  __SpecImpliesBQSSpec_init

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
    /\ __temporal_t_3_unroll = TRUE
    /\ __temporal_t_3_unroll_prev = TRUE
    /\ __temporal_t_2
      = (buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>
        /\ __temporal_t_3)
    /\ __temporal_t_4 \in BOOLEAN
    /\ __saved___temporal_t_4 = __temporal_t_4
    /\ __temporal_t_5 \in BOOLEAN
    /\ __saved___temporal_t_5 = __temporal_t_5
    /\ __temporal_t_5_unroll = TRUE
    /\ __temporal_t_5_unroll_prev = TRUE
    /\ __temporal_t_4
      = (buffer = <<>>
        /\ {
          [ x1347 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1347] ][__x675]:
            __x675 \in
              DOMAIN ([ x1348 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1348] ])
        }
          = {}
        /\ {
          [ x1349 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1349] ][__x676]:
            __x676 \in
              DOMAIN ([ x1350 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1350] ])
        }
          = {}
        /\ __temporal_t_5)
    /\ __temporal_t_1 = (__temporal_t_2 => __temporal_t_4)
    /\ __SpecImpliesBQSSpec_init = __temporal_t_1

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
    /\ __temporal_t_3_unroll' \in BOOLEAN
    /\ (__temporal_t_3
      <=> ((\E p15 \in Producers:
            p15
                \notin {
                  [ x1343 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1343] ][
                    __x673
                  ]:
                    __x673 \in
                      DOMAIN ([
                        x1344 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1344]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p15)
                  /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                    \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
                  /\ waitSeqP' = waitSeqP)
                \/ (Len(buffer) = BufCapacity
                  /\ waitSeqP' = Append(waitSeqP, p15)
                  /\ buffer' = buffer
                  /\ waitSeqC' = waitSeqC)))
          \/ (\E c14 \in Consumers:
            c14
                \notin {
                  [ x1345 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1345] ][
                    __x674
                  ]:
                    __x674 \in
                      DOMAIN ([
                        x1346 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1346]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                    \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
                  /\ waitSeqC' = waitSeqC)
                \/ (buffer = <<>>
                  /\ waitSeqC' = Append(waitSeqC, c14)
                  /\ buffer' = buffer
                  /\ waitSeqP' = waitSeqP)))
          \/ <<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>)
        /\ __temporal_t_3')
    /\ (__temporal_t_3_unroll
      <=> __temporal_t_3_unroll_prev
        /\ (~__InLoop'
          \/ (\E p15 \in Producers:
            p15
                \notin {
                  [ x1343 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1343] ][
                    __x673
                  ]:
                    __x673 \in
                      DOMAIN ([
                        x1344 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1344]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p15)
                  /\ ((waitSeqC = <<>> /\ waitSeqC' = waitSeqC)
                    \/ (waitSeqC /= <<>> /\ waitSeqC' = Tail(waitSeqC)))
                  /\ waitSeqP' = waitSeqP)
                \/ (Len(buffer) = BufCapacity
                  /\ waitSeqP' = Append(waitSeqP, p15)
                  /\ buffer' = buffer
                  /\ waitSeqC' = waitSeqC)))
          \/ (\E c14 \in Consumers:
            c14
                \notin {
                  [ x1345 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1345] ][
                    __x674
                  ]:
                    __x674 \in
                      DOMAIN ([
                        x1346 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1346]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ ((waitSeqP = <<>> /\ waitSeqP' = waitSeqP)
                    \/ (waitSeqP /= <<>> /\ waitSeqP' = Tail(waitSeqP)))
                  /\ waitSeqC' = waitSeqC)
                \/ (buffer = <<>>
                  /\ waitSeqC' = Append(waitSeqC, c14)
                  /\ buffer' = buffer
                  /\ waitSeqP' = waitSeqP)))
          \/ <<buffer, waitSeqC, waitSeqP>>' = <<buffer, waitSeqC, waitSeqP>>))
    /\ __temporal_t_3_unroll_prev' = __temporal_t_3_unroll
    /\ __temporal_t_2'
      = (buffer = <<>>
        /\ waitSeqC = <<>>
        /\ waitSeqP = <<>>
        /\ __temporal_t_3)
    /\ __temporal_t_4' \in BOOLEAN
    /\ __saved___temporal_t_4'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_4 ELSE __temporal_t_4)
    /\ __temporal_t_5' \in BOOLEAN
    /\ __saved___temporal_t_5'
      = (IF __InLoop = __InLoop' THEN __saved___temporal_t_5 ELSE __temporal_t_5)
    /\ __temporal_t_5_unroll' \in BOOLEAN
    /\ (__temporal_t_5
      <=> ((\E p16 \in Producers:
            p16
                \notin {
                  [ x1351 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1351] ][
                    __x677
                  ]:
                    __x677 \in
                      DOMAIN ([
                        x1352 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1352]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p16)
                  /\ (({
                        [ x1353 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1353] ][
                          __x678
                        ]:
                          __x678 \in
                            DOMAIN ([
                              x1354 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1354]
                            ])
                      }
                        = {}
                      /\ {
                        [ x1355 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1355] ][
                          __x679
                        ]:
                          __x679 \in
                            DOMAIN ([
                              x1356 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1356]
                            ])
                      }'
                        = {
                          [ x1357 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1357] ][
                            __x680
                          ]:
                            __x680 \in
                              DOMAIN ([
                                x1358 \in 1 .. Len(waitSeqC) |->
                                  waitSeqC[x1358]
                              ])
                        })
                    \/ ({
                        [ x1359 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1359] ][
                          __x681
                        ]:
                          __x681 \in
                            DOMAIN ([
                              x1360 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1360]
                            ])
                      }
                        /= {}
                      /\ (\E x1361 \in {
                        [ x1362 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1362] ][
                          __x682
                        ]:
                          __x682 \in
                            DOMAIN ([
                              x1363 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1363]
                            ])
                      }:
                        {
                          [ x1364 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1364] ][
                            __x683
                          ]:
                            __x683 \in
                              DOMAIN ([
                                x1365 \in 1 .. Len(waitSeqC) |->
                                  waitSeqC[x1365]
                              ])
                        }'
                          = {
                            [
                              x1366 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1366]
                            ][
                              __x684
                            ]:
                              __x684 \in
                                DOMAIN ([
                                  x1367 \in 1 .. Len(waitSeqC) |->
                                    waitSeqC[x1367]
                                ])
                          }
                            \ {x1361})))
                  /\ {
                    [ x1368 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1368] ][
                      __x685
                    ]:
                      __x685 \in
                        DOMAIN ([
                          x1369 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1369]
                        ])
                  }'
                    = {
                      [ x1370 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1370] ][
                        __x686
                      ]:
                        __x686 \in
                          DOMAIN ([
                            x1371 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1371]
                          ])
                    })
                \/ (Len(buffer) = BufCapacity
                  /\ {
                    [ x1372 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1372] ][
                      __x687
                    ]:
                      __x687 \in
                        DOMAIN ([
                          x1373 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1373]
                        ])
                  }'
                    = {
                      [ x1374 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1374] ][
                        __x688
                      ]:
                        __x688 \in
                          DOMAIN ([
                            x1375 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1375]
                          ])
                    }
                      \union {p16}
                  /\ buffer' = buffer
                  /\ {
                    [ x1376 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1376] ][
                      __x689
                    ]:
                      __x689 \in
                        DOMAIN ([
                          x1377 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1377]
                        ])
                  }'
                    = {
                      [ x1378 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1378] ][
                        __x690
                      ]:
                        __x690 \in
                          DOMAIN ([
                            x1379 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1379]
                          ])
                    })))
          \/ (\E c15 \in Consumers:
            c15
                \notin {
                  [ x1380 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1380] ][
                    __x691
                  ]:
                    __x691 \in
                      DOMAIN ([
                        x1381 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1381]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ (({
                        [ x1382 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1382] ][
                          __x692
                        ]:
                          __x692 \in
                            DOMAIN ([
                              x1383 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1383]
                            ])
                      }
                        = {}
                      /\ {
                        [ x1384 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1384] ][
                          __x693
                        ]:
                          __x693 \in
                            DOMAIN ([
                              x1385 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1385]
                            ])
                      }'
                        = {
                          [ x1386 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1386] ][
                            __x694
                          ]:
                            __x694 \in
                              DOMAIN ([
                                x1387 \in 1 .. Len(waitSeqP) |->
                                  waitSeqP[x1387]
                              ])
                        })
                    \/ ({
                        [ x1388 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1388] ][
                          __x695
                        ]:
                          __x695 \in
                            DOMAIN ([
                              x1389 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1389]
                            ])
                      }
                        /= {}
                      /\ (\E x1390 \in {
                        [ x1391 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1391] ][
                          __x696
                        ]:
                          __x696 \in
                            DOMAIN ([
                              x1392 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1392]
                            ])
                      }:
                        {
                          [ x1393 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1393] ][
                            __x697
                          ]:
                            __x697 \in
                              DOMAIN ([
                                x1394 \in 1 .. Len(waitSeqP) |->
                                  waitSeqP[x1394]
                              ])
                        }'
                          = {
                            [
                              x1395 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1395]
                            ][
                              __x698
                            ]:
                              __x698 \in
                                DOMAIN ([
                                  x1396 \in 1 .. Len(waitSeqP) |->
                                    waitSeqP[x1396]
                                ])
                          }
                            \ {x1390})))
                  /\ {
                    [ x1397 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1397] ][
                      __x699
                    ]:
                      __x699 \in
                        DOMAIN ([
                          x1398 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1398]
                        ])
                  }'
                    = {
                      [ x1399 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1399] ][
                        __x700
                      ]:
                        __x700 \in
                          DOMAIN ([
                            x1400 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1400]
                          ])
                    })
                \/ (buffer = <<>>
                  /\ {
                    [ x1401 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1401] ][
                      __x701
                    ]:
                      __x701 \in
                        DOMAIN ([
                          x1402 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1402]
                        ])
                  }'
                    = {
                      [ x1403 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1403] ][
                        __x702
                      ]:
                        __x702 \in
                          DOMAIN ([
                            x1404 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1404]
                          ])
                    }
                      \union {c15}
                  /\ buffer' = buffer
                  /\ {
                    [ x1405 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1405] ][
                      __x703
                    ]:
                      __x703 \in
                        DOMAIN ([
                          x1406 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1406]
                        ])
                  }'
                    = {
                      [ x1407 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1407] ][
                        __x704
                      ]:
                        __x704 \in
                          DOMAIN ([
                            x1408 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1408]
                          ])
                    })))
          \/ <<
            buffer, {
              [ x1409 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1409] ][__x705]:
                __x705 \in
                  DOMAIN ([ x1410 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1410] ])
            }, {
              [ x1411 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1411] ][__x706]:
                __x706 \in
                  DOMAIN ([ x1412 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1412] ])
            }
          >>'
            = <<
              buffer, {
                [ x1413 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1413] ][__x707]:
                  __x707 \in
                    DOMAIN ([
                      x1414 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1414]
                    ])
              }, {
                [ x1415 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1415] ][__x708]:
                  __x708 \in
                    DOMAIN ([
                      x1416 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1416]
                    ])
              }
            >>)
        /\ __temporal_t_5')
    /\ (__temporal_t_5_unroll
      <=> __temporal_t_5_unroll_prev
        /\ (~__InLoop'
          \/ (\E p16 \in Producers:
            p16
                \notin {
                  [ x1351 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1351] ][
                    __x677
                  ]:
                    __x677 \in
                      DOMAIN ([
                        x1352 \in 1 .. Len(waitSeqP) |->
                          waitSeqP[x1352]
                      ])
                }
              /\ ((Len(buffer) < BufCapacity
                  /\ buffer' = Append(buffer, p16)
                  /\ (({
                        [ x1353 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1353] ][
                          __x678
                        ]:
                          __x678 \in
                            DOMAIN ([
                              x1354 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1354]
                            ])
                      }
                        = {}
                      /\ {
                        [ x1355 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1355] ][
                          __x679
                        ]:
                          __x679 \in
                            DOMAIN ([
                              x1356 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1356]
                            ])
                      }'
                        = {
                          [ x1357 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1357] ][
                            __x680
                          ]:
                            __x680 \in
                              DOMAIN ([
                                x1358 \in 1 .. Len(waitSeqC) |->
                                  waitSeqC[x1358]
                              ])
                        })
                    \/ ({
                        [ x1359 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1359] ][
                          __x681
                        ]:
                          __x681 \in
                            DOMAIN ([
                              x1360 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1360]
                            ])
                      }
                        /= {}
                      /\ (\E x1361 \in {
                        [ x1362 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1362] ][
                          __x682
                        ]:
                          __x682 \in
                            DOMAIN ([
                              x1363 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1363]
                            ])
                      }:
                        {
                          [ x1364 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1364] ][
                            __x683
                          ]:
                            __x683 \in
                              DOMAIN ([
                                x1365 \in 1 .. Len(waitSeqC) |->
                                  waitSeqC[x1365]
                              ])
                        }'
                          = {
                            [
                              x1366 \in 1 .. Len(waitSeqC) |->
                                waitSeqC[x1366]
                            ][
                              __x684
                            ]:
                              __x684 \in
                                DOMAIN ([
                                  x1367 \in 1 .. Len(waitSeqC) |->
                                    waitSeqC[x1367]
                                ])
                          }
                            \ {x1361})))
                  /\ {
                    [ x1368 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1368] ][
                      __x685
                    ]:
                      __x685 \in
                        DOMAIN ([
                          x1369 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1369]
                        ])
                  }'
                    = {
                      [ x1370 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1370] ][
                        __x686
                      ]:
                        __x686 \in
                          DOMAIN ([
                            x1371 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1371]
                          ])
                    })
                \/ (Len(buffer) = BufCapacity
                  /\ {
                    [ x1372 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1372] ][
                      __x687
                    ]:
                      __x687 \in
                        DOMAIN ([
                          x1373 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1373]
                        ])
                  }'
                    = {
                      [ x1374 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1374] ][
                        __x688
                      ]:
                        __x688 \in
                          DOMAIN ([
                            x1375 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1375]
                          ])
                    }
                      \union {p16}
                  /\ buffer' = buffer
                  /\ {
                    [ x1376 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1376] ][
                      __x689
                    ]:
                      __x689 \in
                        DOMAIN ([
                          x1377 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1377]
                        ])
                  }'
                    = {
                      [ x1378 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1378] ][
                        __x690
                      ]:
                        __x690 \in
                          DOMAIN ([
                            x1379 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1379]
                          ])
                    })))
          \/ (\E c15 \in Consumers:
            c15
                \notin {
                  [ x1380 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1380] ][
                    __x691
                  ]:
                    __x691 \in
                      DOMAIN ([
                        x1381 \in 1 .. Len(waitSeqC) |->
                          waitSeqC[x1381]
                      ])
                }
              /\ ((buffer /= <<>>
                  /\ buffer' = Tail(buffer)
                  /\ (({
                        [ x1382 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1382] ][
                          __x692
                        ]:
                          __x692 \in
                            DOMAIN ([
                              x1383 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1383]
                            ])
                      }
                        = {}
                      /\ {
                        [ x1384 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1384] ][
                          __x693
                        ]:
                          __x693 \in
                            DOMAIN ([
                              x1385 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1385]
                            ])
                      }'
                        = {
                          [ x1386 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1386] ][
                            __x694
                          ]:
                            __x694 \in
                              DOMAIN ([
                                x1387 \in 1 .. Len(waitSeqP) |->
                                  waitSeqP[x1387]
                              ])
                        })
                    \/ ({
                        [ x1388 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1388] ][
                          __x695
                        ]:
                          __x695 \in
                            DOMAIN ([
                              x1389 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1389]
                            ])
                      }
                        /= {}
                      /\ (\E x1390 \in {
                        [ x1391 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1391] ][
                          __x696
                        ]:
                          __x696 \in
                            DOMAIN ([
                              x1392 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1392]
                            ])
                      }:
                        {
                          [ x1393 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1393] ][
                            __x697
                          ]:
                            __x697 \in
                              DOMAIN ([
                                x1394 \in 1 .. Len(waitSeqP) |->
                                  waitSeqP[x1394]
                              ])
                        }'
                          = {
                            [
                              x1395 \in 1 .. Len(waitSeqP) |->
                                waitSeqP[x1395]
                            ][
                              __x698
                            ]:
                              __x698 \in
                                DOMAIN ([
                                  x1396 \in 1 .. Len(waitSeqP) |->
                                    waitSeqP[x1396]
                                ])
                          }
                            \ {x1390})))
                  /\ {
                    [ x1397 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1397] ][
                      __x699
                    ]:
                      __x699 \in
                        DOMAIN ([
                          x1398 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1398]
                        ])
                  }'
                    = {
                      [ x1399 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1399] ][
                        __x700
                      ]:
                        __x700 \in
                          DOMAIN ([
                            x1400 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1400]
                          ])
                    })
                \/ (buffer = <<>>
                  /\ {
                    [ x1401 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1401] ][
                      __x701
                    ]:
                      __x701 \in
                        DOMAIN ([
                          x1402 \in 1 .. Len(waitSeqC) |->
                            waitSeqC[x1402]
                        ])
                  }'
                    = {
                      [ x1403 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1403] ][
                        __x702
                      ]:
                        __x702 \in
                          DOMAIN ([
                            x1404 \in 1 .. Len(waitSeqC) |->
                              waitSeqC[x1404]
                          ])
                    }
                      \union {c15}
                  /\ buffer' = buffer
                  /\ {
                    [ x1405 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1405] ][
                      __x703
                    ]:
                      __x703 \in
                        DOMAIN ([
                          x1406 \in 1 .. Len(waitSeqP) |->
                            waitSeqP[x1406]
                        ])
                  }'
                    = {
                      [ x1407 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1407] ][
                        __x704
                      ]:
                        __x704 \in
                          DOMAIN ([
                            x1408 \in 1 .. Len(waitSeqP) |->
                              waitSeqP[x1408]
                          ])
                    })))
          \/ <<
            buffer, {
              [ x1409 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1409] ][__x705]:
                __x705 \in
                  DOMAIN ([ x1410 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1410] ])
            }, {
              [ x1411 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1411] ][__x706]:
                __x706 \in
                  DOMAIN ([ x1412 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1412] ])
            }
          >>'
            = <<
              buffer, {
                [ x1413 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1413] ][__x707]:
                  __x707 \in
                    DOMAIN ([
                      x1414 \in 1 .. Len(waitSeqC) |->
                        waitSeqC[x1414]
                    ])
              }, {
                [ x1415 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1415] ][__x708]:
                  __x708 \in
                    DOMAIN ([
                      x1416 \in 1 .. Len(waitSeqP) |->
                        waitSeqP[x1416]
                    ])
              }
            >>))
    /\ __temporal_t_5_unroll_prev' = __temporal_t_5_unroll
    /\ __temporal_t_4'
      = (buffer = <<>>
        /\ {
          [ x1347 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1347] ][__x675]:
            __x675 \in
              DOMAIN ([ x1348 \in 1 .. Len(waitSeqC) |-> waitSeqC[x1348] ])
        }
          = {}
        /\ {
          [ x1349 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1349] ][__x676]:
            __x676 \in
              DOMAIN ([ x1350 \in 1 .. Len(waitSeqP) |-> waitSeqP[x1350] ])
        }
          = {}
        /\ __temporal_t_5)
    /\ __temporal_t_1' = (__temporal_t_2 => __temporal_t_4)
    /\ UNCHANGED __SpecImpliesBQSSpec_init

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
    /\ (__temporal_t_3_unroll => __temporal_t_3)
    /\ __temporal_t_3_unroll_prev = __temporal_t_3_unroll
    /\ __temporal_t_4 = __saved___temporal_t_4
    /\ __temporal_t_5 = __saved___temporal_t_5
    /\ (__temporal_t_5_unroll => __temporal_t_5)
    /\ __temporal_t_5_unroll_prev = __temporal_t_5_unroll

(*
  @type: (() => Bool);
*)
SpecImpliesBQSSpec == __LoopOK => __SpecImpliesBQSSpec_init

================================================================================
