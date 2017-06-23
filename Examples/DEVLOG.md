
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

