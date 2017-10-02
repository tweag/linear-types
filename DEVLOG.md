
[2017.06.23] {Squeezing the allocation out of packTree}
-------------------------------------------------------

Here is the current .dump-simpl output for the packTree loop.


```Haskell
$wgo [InlPrag=[0], Occ=LoopBreaker]
  :: forall (r :: [*]) t.
     Tree -> Addr# -> Addr# -> (# Addr#, Addr# #)
[GblId, Arity=3, Caf=NoCafRefs, Str=<S,1*U><L,U><L,U>]
$wgo
  = \ (@ (r_sgiH :: [*]))
      (@ t_sgiI)
      (w_sgiJ :: Tree)
      (ww_sgiN :: Addr#)
      (ww1_sgiO :: Addr#) ->
      case (NotUnrestricted @ WByteArray (WBA ww_sgiN ww1_sgiO))
           `cast` (UnsafeCo representational
                     (NotUnrestricted WByteArray) (Unrestricted WByteArray)
                   :: (NotUnrestricted WByteArray :: *)
                      ~R#
                      (Unrestricted WByteArray :: *))
      of
      { Unrestricted ds_sgAp ->
      case w_sgiJ of {
        Leaf a_afjG ->
          case a_afjG of { I# ww3_sgiw ->
          $wwriteLeaf @ r_sgiH @ t_sgiI ww3_sgiw ww_sgiN ww1_sgiO
          };
        Branch left_afjI right_afjJ ->
          src<libraries/base/Unsafe/Coerce.hs:58:1-43>
          src<libraries/base/Unsafe/Coerce.hs:38:1-14>
          case ds_sgAp of { WBA dt_ddvo dt1_ddvp ->
          src<libraries/base/GHC/IO/Unsafe.hs:104:1-64>
          case runRW#
                 @ ('TupleRep '['TupleRep '[], 'LiftedRep])
                 @ (# State# RealWorld, () #)
                 (\ (eta_adXb [OS=OneShot] :: State# RealWorld) ->
                    src<libraries/base/Foreign/Storable.hs:146:4-31>
                    src<libraries/base/Foreign/Storable.hs:204:215-244>
                    src<libraries/base/GHC/Ptr.hs:63:1-16>
                    case writeWord8OffAddr# @ RealWorld dt_ddvo 0# 111## eta_adXb
                    of s2_adXk
                    { __DEFAULT ->
                    (# s2_adXk, () #)
                    })
          of
          { (# ipv_a7jQ, ipv1_a7jR #) ->
          src<libraries/base/GHC/IO/Unsafe.hs:104:64>
          case ipv1_a7jR of { () ->
          src<libraries/base/GHC/Ptr.hs:67:1-50>
          src<libraries/base/Foreign/Storable.hs:204:57-71>
          case $wgo
                 @ (Tree : r_sgiH)
                 @ t_sgiI
                 left_afjI
                 (plusAddr# dt_ddvo 1#)
                 dt1_ddvp
          of
          { (# ww3_sgks, ww4_sgkt #) ->
          $wgo @ r_sgiH @ t_sgiI right_afjJ ww3_sgks ww4_sgkt
          }
          }
          }
          }
      }
      }
```

And for the allocating ByteArray-writing loop, here's the STG:

```
main4 =
    \r [c]
        let {
          $wgo =
              sat-only \r [ww] 
                  case ww of wild {
                    __DEFAULT -> 
                        case -# [wild 1#] of sat {
                          __DEFAULT ->
                              case $wgo sat of wild1 {
                                WBA dt dt1 -> 
                                    case
                                        case readIntOffAddr# [dt 0# realWorld#] of {
                                          (#,#) ipv ipv1 -> 
                                              case plusAddr# [dt1 ipv1] of sat {
                                                __DEFAULT ->
                                                    case
                                                        writeWord8OffAddr# [sat 0# 33## ipv]
                                                    of
                                                    s2
                                                    { __DEFAULT -> 
                                                          case readIntOffAddr# [dt 0# s2] of {
                                                            (#,#) ipv2 ipv3 -> 
                                                                case +# [ipv3 1#] of sat {
                                                                  __DEFAULT ->
                                                                      case
                                                                          writeIntOffAddr# [dt
                                                                                            0#
                                                                                            sat
                                                                                            ipv2]
                                                                      of
                                                                      s1
                                                                      { __DEFAULT -> 
                                                                            (#,#) [s1 wild1];
                                                                      };
                                                                };
                                                          };
                                                    };
                                              };
                                        }
                                    of
                                    { (#,#) _ ipv1 -> ipv1;
                                    };
                              };
                        };
                    0# -> c;
                  };
        } in 
          case $wgo 10000# of {
            WBA ww1 ww2 ->
                case $wfreeze ww1 ww2 of { Unit# ww4 -> Unrestricted [ww4]; };
          };
```

That looks pretty good.  I don't see where the allocation is.

Below is `packTree` Core, which is also allocating, and I don't see where.

```Haskell
Rec {
-- RHS size: {terms: 144, types: 238, coercions: 11, joins: 0/0}
$wgo
$wgo
  = \ @ r @ t w ww ww1 ->
      case w of {
        Leaf a -> 
          case runRW#
                 (\ s -> 
                    case readIntOffAddr# ww 0# s of { (# ipv, ipv1 #) -> 
                    case writeWord8OffAddr# (plusAddr# ww1 ipv1) 0# 100## ipv of s2
                    { __DEFAULT -> 
                    case readIntOffAddr# ww 0# s2 of { (# ipv4, ipv5 #) -> 
                    case writeIntOffAddr# ww 0# (+# ipv5 1#) ipv4 of s1 { __DEFAULT -> (# s1, WBA ww ww1 #)
                    }
                    }
                    }
                    })
          of
          { (# ipv, ipv1 #) -> 
          case ipv1 of wild1 { WBA dt dt1 -> 
          case runRW#
                 (\ s -> 
                    case readIntOffAddr# dt 0# s of { (# ipv2, ipv3 #) -> 
                    case a of { I# x -> 
                    case writeIntOffAddr# (plusAddr# dt1 ipv3) 0# x ipv2 of s2
                    { __DEFAULT -> 
                    case readIntOffAddr# dt 0# s2 of { (# ipv4, ipv5 #) -> 
                    case writeIntOffAddr# dt 0# (+# ipv5 8#) ipv4 of s1 { __DEFAULT -> (# s1, wild1 #)
                    }
                    }
                    }
                    }
                    })
          of
          { (# ipv2, ipv3 #) -> ( ipv3) `cast` <Co:4>
          }
          }
          };
        Branch left right -> 
          case runRW#
                 (\ s -> 
                    case readIntOffAddr# ww 0# s of { (# ipv, ipv1 #) -> 
                    case writeWord8OffAddr# (plusAddr# ww1 ipv1) 0# 111## ipv of s2
                    { __DEFAULT -> 
                    case readIntOffAddr# ww 0# s2 of { (# ipv4, ipv5 #) -> 
                    case writeIntOffAddr# ww 0# (+# ipv5 1#) ipv4 of s1 { __DEFAULT -> (# s1, WBA ww ww1 #)
                    }
                    }
                    }
                    })
          of
          { (# ipv, ipv1 #) -> 
          case ipv1 of { WBA ww3 ww4 ->
          case ($wgo left ww3 ww4) `cast` <Co:7> of { WBA ww6 ww7 ->
          $wgo right ww6 ww7
          }
          }
          }
      }
end Rec }

-- RHS size: {terms: 23, types: 48, coercions: 23, joins: 0/0}
packTree
packTree
  = \ tr0 ->
      case alloc
             regionSize
             (\ bs ->
                case bs of { WBA ww1 ww2 ->
                case ($wgo tr0 ww1 ww2) `cast` <Co:4> of { WBA ww4 ww5 ->
                case $wfreeze ww4 ww5 of { (# ww7 #) ->
                Unrestricted (ww7 `cast` <Co:9>)
                }
                }
                })
      of
      { Unrestricted x ->
      x `cast` <Co:10>
      }
```

And here's the STG to go with that:

```Haskell
$wgo :: forall (r :: [*]) t. Tree -> Addr# -> Addr# -> Needs r t =
    \r [w ww ww1]
        case w of {
          Leaf a -> 
              case
                  case readIntOffAddr# [ww 0# realWorld#] of {
                    (#,#) ipv ipv1 -> 
                        case plusAddr# [ww1 ipv1] of sat {
                          __DEFAULT ->
                              case writeWord8OffAddr# [sat 0# 100## ipv] of s2 {
                                __DEFAULT -> 
                                    case readIntOffAddr# [ww 0# s2] of {
                                      (#,#) ipv4 ipv5 -> 
                                          case +# [ipv5 1#] of sat {
                                            __DEFAULT ->
                                                case writeIntOffAddr# [ww 0# sat ipv4] of s1 {
                                                  __DEFAULT -> 
                                                      let {
                                                        sat :: WByteArray = NO_CCS WBA! [ww ww1];
                                                      } in 
                                                        (#,#) [s1 sat];
                                                };
                                          };
                                    };
                              };
                        };
                  }
              of
              { (#,#) _ ipv1 -> 
                    case ipv1 of wild1 {
                      WBA dt dt1 -> 
                          case
                              case readIntOffAddr# [dt 0# realWorld#] of {
                                (#,#) ipv2 ipv3 -> 
                                    case a of {
                                      I# x -> 
                                          case plusAddr# [dt1 ipv3] of sat {
                                            __DEFAULT ->
                                                case writeIntOffAddr# [sat 0# x ipv2] of s2 {
                                                  __DEFAULT -> 
                                                      case readIntOffAddr# [dt 0# s2] of {
                                                        (#,#) ipv4 ipv5 -> 
                                                            case +# [ipv5 8#] of sat {
                                                              __DEFAULT ->
                                                                  case
                                                                      writeIntOffAddr# [dt
                                                                                        0#
                                                                                        sat
                                                                                        ipv4]
                                                                  of
                                                                  s1
                                                                  { __DEFAULT -> 
                                                                        (#,#) [s1 wild1];
                                                                  };
                                                            };
                                                      };
                                                };
                                          };
                                    };
                              }
                          of { (#,#) _ ipv3 ->  ipv3;
                          };
                    };
              };
          Branch left right -> 
              case
                  case readIntOffAddr# [ww 0# realWorld#] of {
                    (#,#) ipv ipv1 -> 
                        case plusAddr# [ww1 ipv1] of sat {
                          __DEFAULT ->
                              case writeWord8OffAddr# [sat 0# 111## ipv] of s2 {
                                __DEFAULT -> 
                                    case readIntOffAddr# [ww 0# s2] of {
                                      (#,#) ipv4 ipv5 -> 
                                          case +# [ipv5 1#] of sat {
                                            __DEFAULT ->
                                                case writeIntOffAddr# [ww 0# sat ipv4] of s1 {
                                                  __DEFAULT -> 
                                                      let {
                                                        sat :: WByteArray = NO_CCS WBA! [ww ww1];
                                                      } in 
                                                        (#,#) [s1 sat];
                                                };
                                          };
                                    };
                              };
                        };
                  }
              of
              { (#,#) _ ipv1 -> 
                    case ipv1 of {
                      WBA ww3 ww4 ->
                          case $wgo left ww3 ww4 of { WBA ww6 ww7 -> $wgo right ww6 ww7; };
                    };
              };
        };

packTree :: Tree -> Packed Tree =
    \r [tr0]
        let {
          sat :: WByteArray ⊸ Unrestricted (Has '[Tree]) =
              \r [bs]
                  case bs of {
                    WBA ww1 ww2 ->
                        case $wgo tr0 ww1 ww2 of {
                          WBA ww4 ww5 ->
                              case $wfreeze ww4 ww5 of { Unit# ww7 -> Unrestricted [ww7]; };
                        };
                  };
        } in  case alloc regionSize sat of { Unrestricted x -> x; };
```

Ah, ok, this bit could be the culprit:

     let { sat :: WByteArray = NO_CCS WBA! [ww ww1]; }
     in (#,#) [s1 sat];

--------------------------------------------------------------------------------

Ok, now I'm getting some bad code for SumTree having to do with how
the results of "readC" flow back to the caller.  See the "W8#" boxes
below in the STG.

```Haskell
$wgo1
  :: forall (r :: [*]).
     Addr# -> ForeignPtrContents -> Int# -> Int# -> (# Int, Has r #) =
    \r [ww ww1 ww2 ww3] 
        case plusAddr# [ww ww2] of sat {
          __DEFAULT ->
              case
                  case readWord8OffAddr# [sat 0# realWorld#] of {
                    (#,#) ipv ipv1 ->
                        case touch# [ww1 ipv] of s' {
                          __DEFAULT ->
                              let { sat :: TagTy = NO_CCS W8#! [ipv1]; } in  (#,#) [s' sat];
                        };
                  }
              of
              { (#,#) _ ipv1 -> 
                    case ipv1 of {
                      W8# x -> 
                          case x of {
                            __DEFAULT -> patError lvl18;
                            100## ->
                                let {
                                  w1 :: Has (Int : r) =
                                      \u [] 
                                          case >=# [1# ww3] of sat {
                                            __DEFAULT ->
                                                case tagToEnum# [sat] of {
                                                  False -> 
                                                      case -# [ww3 1#] of sat {
                                                        __DEFAULT ->
                                                            case +# [ww2 1#] of sat {
                                                              __DEFAULT -> PS [ww ww1 sat sat];
                                                            };
                                                      };
                                                  True -> 
                                                      empty;
                                                };
                                          }; } in
                                let {
                                  sat :: Has r =
                                      \u [] 
                                          case w1 of {
                                            PS dt dt1 dt2 dt3 -> 
                                                case >=# [8# dt3] of sat {
                                                  __DEFAULT ->
                                                      case tagToEnum# [sat] of {
                                                        False -> 
                                                            case -# [dt3 8#] of sat {
                                                              __DEFAULT ->
                                                                  case +# [dt2 8#] of sat {
                                                                    __DEFAULT ->
                                                                        PS [dt dt1 sat sat];
                                                                  };
                                                            };
                                                        True -> 
                                                            empty;
                                                      };
                                                };
                                          }; } in
                                let {
                                  sat :: Int =
                                      \u [] 
                                          case
                                              case w1 of {
                                                PS dt dt1 dt2 _ -> 
                                                    case plusAddr# [dt dt2] of sat {
                                                      __DEFAULT ->
                                                          case
                                                              readIntOffAddr# [sat 0# realWorld#]
                                                          of
                                                          { (#,#) ipv2 ipv3 ->
                                                                case touch# [dt1 ipv2] of s' {
                                                                  __DEFAULT ->
                                                                      let {
                                                                        sat :: Int =
                                                                            NO_CCS I#! [ipv3];
                                                                      } in  (#,#) [s' sat];
                                                                };
                                                          };
                                                    };
                                              }
                                          of
                                          { (#,#) _ ipv3 -> ipv3;
                                          };
                                } in  (#,#) [sat sat];
                            111## -> 
                                case >=# [1# ww3] of sat {
                                  __DEFAULT ->
                                      case tagToEnum# [sat] of {
                                        False -> 
                                            case -# [ww3 1#] of sat {
                                              __DEFAULT ->
                                                  case +# [ww2 1#] of sat {
                                                    __DEFAULT -> poly_$j ww ww1 sat sat;
                                                  };
                                            };
                                        True -> 
                                            poly_$j __NULL $fMonoidByteString1 0# 0#;
                                      };
                                };
                          };
                    };
              };
        };

sumTree_go
  :: forall (r :: [*]). Has (Tree : r) -> (# Int, Has r #) =
    \r [w] case w of { PS ww1 ww2 ww3 ww4 -> $wgo1 ww1 ww2 ww3 ww4; };

sumTree :: Packed Tree -> Int =
    \r [t]
        case t of {
          PS ww1 ww2 ww3 ww4 ->
              case $wgo1 ww1 ww2 ww3 ww4 of { (#,#) ipv _ -> ipv; };
        };
```



[2017.06.26] {Continued issues with unboxing optimizations}
------------------------------------------------------------

I've contorted the bytestring-reading code to use a monad with an
implicit cursor into a designated stream being consumed (state monad).

But I'm still getting an inner loop for sumTree that looks like this:


```Haskell
$wgo3
  :: Addr#
     -> Addr# -> State# RealWorld -> (# State# RealWorld, Int #)
$wgo3
  = \ (ww :: Addr#) (ww1 :: Addr#) (w :: State# RealWorld) -> 
      case readIntOffAddr# ww1 0# w of { (# ipv, ipv1 #) -> 
      case readWord8OffAddr# (plusAddr# ww ipv1) 0# ipv of
      { (# ipv2, ipv3 #) -> 
      case readIntOffAddr# ww1 0# ipv2 of { (# ipv4, ipv5 #) -> 
      case writeIntOffAddr# ww1 0# (+# ipv5 1#) ipv4 of s2 { __DEFAULT -> 
      case ipv3 of {
        __DEFAULT -> 
          case $wgo3 ww ww1 s2 of { (# ipv7, ipv8 #) -> 
          case ipv8 of { I# ipv9 -> 
          case $wgo3 ww ww1 ipv7 of { (# ipv10, ipv11 #) -> 
          case ipv11 of { I# ipv12 -> (# ipv10, I# (+# ipv9 ipv12) #)
          }
          }
          }
          };
        100## -> 
          case readIntOffAddr# ww1 0# s2 of { (# ipv7, ipv8 #) -> 
          case readIntOffAddr# (plusAddr# ww ipv8) 0# ipv7 of
          { (# ipv9, ipv10 #) -> 
          case readIntOffAddr# ww1 0# ipv9 of { (# ipv11, ipv12 #) -> 
          case writeIntOffAddr# ww1 0# (+# ipv12 8#) ipv11 of s1
          { __DEFAULT -> (# s1, I# ipv10 #)
          }
          }
          }
          }
      }
      }
      }
      }
      }
```

I thought the Int being returned strictly should be enough for the
worker to operate entirely on `Int#`.  But it seems there is a problem
with this story and we end up with `Int` return value instead.



