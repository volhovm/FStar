open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> subst1
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { tcenv = env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___363_127 = a  in
              let uu____128 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___363_127.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___363_127.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____128
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____141 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____141
             then
               (d "Elaborating extra WP combinators";
                (let uu____147 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____147))
             else ());
            (let rec collect_binders t =
               let uu____166 =
                 let uu____167 =
                   let uu____170 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____170
                    in
                 uu____167.FStar_Syntax_Syntax.n  in
               match uu____166 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____205) -> t1
                     | FStar_Syntax_Syntax.GTotal (t1,uu____215) -> t1
                     | uu____224 ->
                         let uu____225 =
                           let uu____227 =
                             FStar_Syntax_Print.comp_to_string comp  in
                           Prims.strcat "wp_a contains non-Tot arrow: "
                             uu____227
                            in
                         failwith uu____225
                      in
                   let uu____230 = collect_binders rest  in
                   FStar_List.append bs uu____230
               | FStar_Syntax_Syntax.Tm_type uu____245 -> []
               | uu____252 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____279 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____279 FStar_Syntax_Util.name_binders
                in
             (let uu____305 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____305
              then
                let uu____309 =
                  let uu____311 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____311  in
                d uu____309
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____349 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____349 with
                | (sigelt,fv) ->
                    ((let uu____357 =
                        let uu____360 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____360
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____357);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____484  ->
                     match uu____484 with
                     | (t,b) ->
                         let uu____498 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____498))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____537 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____537))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____571 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____571)
                 in
              let uu____574 =
                let uu____591 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____616 =
                        let uu____619 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____619  in
                      FStar_Syntax_Util.arrow gamma uu____616  in
                    let uu____620 =
                      let uu____621 =
                        let uu____630 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____637 =
                          let uu____646 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____646]  in
                        uu____630 :: uu____637  in
                      FStar_List.append binders uu____621  in
                    FStar_Syntax_Util.abs uu____620 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____677 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____678 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____677, uu____678)  in
                match uu____591 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____720 =
                        let uu____721 =
                          let uu____738 =
                            let uu____749 =
                              FStar_List.map
                                (fun uu____771  ->
                                   match uu____771 with
                                   | (bv,uu____783) ->
                                       let uu____788 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____789 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____788, uu____789)) binders
                               in
                            let uu____791 =
                              let uu____798 =
                                let uu____803 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____804 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____803, uu____804)  in
                              let uu____806 =
                                let uu____813 =
                                  let uu____818 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____818)  in
                                [uu____813]  in
                              uu____798 :: uu____806  in
                            FStar_List.append uu____749 uu____791  in
                          (fv, uu____738)  in
                        FStar_Syntax_Syntax.Tm_app uu____721  in
                      mk1 uu____720  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____574 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____891 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____891
                       in
                    let ret1 =
                      let uu____896 =
                        let uu____897 =
                          let uu____900 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____900  in
                        FStar_Syntax_Util.residual_tot uu____897  in
                      FStar_Pervasives_Native.Some uu____896  in
                    let body =
                      let uu____904 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____904 ret1  in
                    let uu____907 =
                      let uu____908 = mk_all_implicit binders  in
                      let uu____915 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____908 uu____915  in
                    FStar_Syntax_Util.abs uu____907 body ret1  in
                  let c_pure1 =
                    let uu____953 = mk_lid "pure"  in
                    register env1 uu____953 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____963 =
                        let uu____964 =
                          let uu____965 =
                            let uu____974 =
                              let uu____981 =
                                let uu____982 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____982
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____981  in
                            [uu____974]  in
                          let uu____995 =
                            let uu____998 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____998  in
                          FStar_Syntax_Util.arrow uu____965 uu____995  in
                        mk_gctx uu____964  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____963
                       in
                    let r =
                      let uu____1001 =
                        let uu____1002 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1002  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____1001
                       in
                    let ret1 =
                      let uu____1007 =
                        let uu____1008 =
                          let uu____1011 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1011  in
                        FStar_Syntax_Util.residual_tot uu____1008  in
                      FStar_Pervasives_Native.Some uu____1007  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____1021 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____1024 =
                          let uu____1035 =
                            let uu____1038 =
                              let uu____1039 =
                                let uu____1040 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____1040
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1039  in
                            [uu____1038]  in
                          FStar_List.append gamma_as_args uu____1035  in
                        FStar_Syntax_Util.mk_app uu____1021 uu____1024  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____1043 =
                      let uu____1044 = mk_all_implicit binders  in
                      let uu____1051 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1044 uu____1051  in
                    FStar_Syntax_Util.abs uu____1043 outer_body ret1  in
                  let c_app1 =
                    let uu____1103 = mk_lid "app"  in
                    register env1 uu____1103 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1115 =
                        let uu____1124 =
                          let uu____1131 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1131  in
                        [uu____1124]  in
                      let uu____1144 =
                        let uu____1147 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1147  in
                      FStar_Syntax_Util.arrow uu____1115 uu____1144  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1151 =
                        let uu____1152 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1152  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1151
                       in
                    let ret1 =
                      let uu____1157 =
                        let uu____1158 =
                          let uu____1161 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1161  in
                        FStar_Syntax_Util.residual_tot uu____1158  in
                      FStar_Pervasives_Native.Some uu____1157  in
                    let uu____1162 =
                      let uu____1163 = mk_all_implicit binders  in
                      let uu____1170 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1163 uu____1170  in
                    let uu____1221 =
                      let uu____1224 =
                        let uu____1235 =
                          let uu____1238 =
                            let uu____1239 =
                              let uu____1250 =
                                let uu____1253 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1253]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1250
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1239  in
                          let uu____1262 =
                            let uu____1265 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1265]  in
                          uu____1238 :: uu____1262  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1235
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1224  in
                    FStar_Syntax_Util.abs uu____1162 uu____1221 ret1  in
                  let c_lift11 =
                    let uu____1275 = mk_lid "lift1"  in
                    register env1 uu____1275 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1289 =
                        let uu____1298 =
                          let uu____1305 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1305  in
                        let uu____1306 =
                          let uu____1315 =
                            let uu____1322 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1322  in
                          [uu____1315]  in
                        uu____1298 :: uu____1306  in
                      let uu____1341 =
                        let uu____1344 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1344  in
                      FStar_Syntax_Util.arrow uu____1289 uu____1341  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1348 =
                        let uu____1349 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1349  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1348
                       in
                    let a2 =
                      let uu____1352 =
                        let uu____1353 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1353  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1352
                       in
                    let ret1 =
                      let uu____1358 =
                        let uu____1359 =
                          let uu____1362 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1362  in
                        FStar_Syntax_Util.residual_tot uu____1359  in
                      FStar_Pervasives_Native.Some uu____1358  in
                    let uu____1363 =
                      let uu____1364 = mk_all_implicit binders  in
                      let uu____1371 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1364 uu____1371  in
                    let uu____1436 =
                      let uu____1439 =
                        let uu____1450 =
                          let uu____1453 =
                            let uu____1454 =
                              let uu____1465 =
                                let uu____1468 =
                                  let uu____1469 =
                                    let uu____1480 =
                                      let uu____1483 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1483]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1480
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1469
                                   in
                                let uu____1492 =
                                  let uu____1495 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1495]  in
                                uu____1468 :: uu____1492  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1465
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1454  in
                          let uu____1504 =
                            let uu____1507 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1507]  in
                          uu____1453 :: uu____1504  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1450
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1439  in
                    FStar_Syntax_Util.abs uu____1363 uu____1436 ret1  in
                  let c_lift21 =
                    let uu____1517 = mk_lid "lift2"  in
                    register env1 uu____1517 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1529 =
                        let uu____1538 =
                          let uu____1545 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1545  in
                        [uu____1538]  in
                      let uu____1558 =
                        let uu____1561 =
                          let uu____1562 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1562  in
                        FStar_Syntax_Syntax.mk_Total uu____1561  in
                      FStar_Syntax_Util.arrow uu____1529 uu____1558  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1568 =
                        let uu____1569 =
                          let uu____1572 =
                            let uu____1573 =
                              let uu____1582 =
                                let uu____1589 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1589
                                 in
                              [uu____1582]  in
                            let uu____1602 =
                              let uu____1605 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1605  in
                            FStar_Syntax_Util.arrow uu____1573 uu____1602  in
                          mk_ctx uu____1572  in
                        FStar_Syntax_Util.residual_tot uu____1569  in
                      FStar_Pervasives_Native.Some uu____1568  in
                    let e1 =
                      let uu____1607 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1607
                       in
                    let body =
                      let uu____1612 =
                        let uu____1613 =
                          let uu____1622 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1622]  in
                        FStar_List.append gamma uu____1613  in
                      let uu____1647 =
                        let uu____1650 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1653 =
                          let uu____1664 =
                            let uu____1665 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1665  in
                          let uu____1666 = args_of_binders1 gamma  in
                          uu____1664 :: uu____1666  in
                        FStar_Syntax_Util.mk_app uu____1650 uu____1653  in
                      FStar_Syntax_Util.abs uu____1612 uu____1647 ret1  in
                    let uu____1669 =
                      let uu____1670 = mk_all_implicit binders  in
                      let uu____1677 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1670 uu____1677  in
                    FStar_Syntax_Util.abs uu____1669 body ret1  in
                  let c_push1 =
                    let uu____1722 = mk_lid "push"  in
                    register env1 uu____1722 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1749 =
                        let uu____1750 =
                          let uu____1767 = args_of_binders1 binders  in
                          (c, uu____1767)  in
                        FStar_Syntax_Syntax.Tm_app uu____1750  in
                      mk1 uu____1749
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1796 =
                        let uu____1797 =
                          let uu____1806 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1813 =
                            let uu____1822 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1822]  in
                          uu____1806 :: uu____1813  in
                        let uu____1847 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1797 uu____1847  in
                      FStar_Syntax_Syntax.mk_Total uu____1796  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1852 =
                      let uu____1853 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1853  in
                    let uu____1868 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1873 =
                        let uu____1876 =
                          let uu____1887 =
                            let uu____1890 =
                              let uu____1891 =
                                let uu____1902 =
                                  let uu____1911 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1911  in
                                [uu____1902]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1891  in
                            [uu____1890]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1887
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1876  in
                      FStar_Syntax_Util.ascribe uu____1873
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1852 uu____1868
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1955 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1955 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1972 =
                        let uu____1983 =
                          let uu____1986 =
                            let uu____1987 =
                              let uu____1998 =
                                let uu____2001 =
                                  let uu____2002 =
                                    let uu____2013 =
                                      let uu____2022 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2022
                                       in
                                    [uu____2013]  in
                                  FStar_Syntax_Util.mk_app l_and uu____2002
                                   in
                                [uu____2001]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1998
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1987  in
                          let uu____2047 =
                            let uu____2050 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2050]  in
                          uu____1986 :: uu____2047  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1983
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1972  in
                    let uu____2059 =
                      let uu____2060 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2060  in
                    FStar_Syntax_Util.abs uu____2059 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____2076 = mk_lid "wp_assert"  in
                    register env1 uu____2076 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____2093 =
                        let uu____2104 =
                          let uu____2107 =
                            let uu____2108 =
                              let uu____2119 =
                                let uu____2122 =
                                  let uu____2123 =
                                    let uu____2134 =
                                      let uu____2143 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2143
                                       in
                                    [uu____2134]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2123
                                   in
                                [uu____2122]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2119
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2108  in
                          let uu____2168 =
                            let uu____2171 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2171]  in
                          uu____2107 :: uu____2168  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2104
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2093  in
                    let uu____2180 =
                      let uu____2181 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2181  in
                    FStar_Syntax_Util.abs uu____2180 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2197 = mk_lid "wp_assume"  in
                    register env1 uu____2197 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2210 =
                        let uu____2219 =
                          let uu____2226 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2226  in
                        [uu____2219]  in
                      let uu____2239 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2210 uu____2239  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2247 =
                        let uu____2258 =
                          let uu____2261 =
                            let uu____2262 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2262  in
                          let uu____2281 =
                            let uu____2284 =
                              let uu____2285 =
                                let uu____2296 =
                                  let uu____2299 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2299]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2296
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2285  in
                            [uu____2284]  in
                          uu____2261 :: uu____2281  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2258
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2247  in
                    let uu____2316 =
                      let uu____2317 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2317  in
                    FStar_Syntax_Util.abs uu____2316 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2333 = mk_lid "wp_close"  in
                    register env1 uu____2333 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2344 =
                      let uu____2345 =
                        let uu____2346 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2346
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2345  in
                    FStar_Pervasives_Native.Some uu____2344  in
                  let mk_forall1 x body =
                    let uu____2358 =
                      let uu____2365 =
                        let uu____2366 =
                          let uu____2383 =
                            let uu____2394 =
                              let uu____2403 =
                                let uu____2404 =
                                  let uu____2405 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2405]  in
                                FStar_Syntax_Util.abs uu____2404 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2403  in
                            [uu____2394]  in
                          (FStar_Syntax_Util.tforall, uu____2383)  in
                        FStar_Syntax_Syntax.Tm_app uu____2366  in
                      FStar_Syntax_Syntax.mk uu____2365  in
                    uu____2358 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2466 =
                      let uu____2467 = FStar_Syntax_Subst.compress t  in
                      uu____2467.FStar_Syntax_Syntax.n  in
                    match uu____2466 with
                    | FStar_Syntax_Syntax.Tm_type uu____2471 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2504  ->
                              match uu____2504 with
                              | (b,uu____2513) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2518 -> true  in
                  let rec is_monotonic t =
                    let uu____2531 =
                      let uu____2532 = FStar_Syntax_Subst.compress t  in
                      uu____2532.FStar_Syntax_Syntax.n  in
                    match uu____2531 with
                    | FStar_Syntax_Syntax.Tm_type uu____2536 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2569  ->
                              match uu____2569 with
                              | (b,uu____2578) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2583 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2657 =
                      let uu____2658 = FStar_Syntax_Subst.compress t1  in
                      uu____2658.FStar_Syntax_Syntax.n  in
                    match uu____2657 with
                    | FStar_Syntax_Syntax.Tm_type uu____2663 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2666);
                                      FStar_Syntax_Syntax.pos = uu____2667;
                                      FStar_Syntax_Syntax.vars = uu____2668;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2712 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2712
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2722 =
                              let uu____2725 =
                                let uu____2736 =
                                  let uu____2745 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2745  in
                                [uu____2736]  in
                              FStar_Syntax_Util.mk_app x uu____2725  in
                            let uu____2762 =
                              let uu____2765 =
                                let uu____2776 =
                                  let uu____2785 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2785  in
                                [uu____2776]  in
                              FStar_Syntax_Util.mk_app y uu____2765  in
                            mk_rel1 b uu____2722 uu____2762  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2809 =
                               let uu____2812 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2815 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2812 uu____2815  in
                             let uu____2818 =
                               let uu____2821 =
                                 let uu____2824 =
                                   let uu____2835 =
                                     let uu____2844 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2844
                                      in
                                   [uu____2835]  in
                                 FStar_Syntax_Util.mk_app x uu____2824  in
                               let uu____2861 =
                                 let uu____2864 =
                                   let uu____2875 =
                                     let uu____2884 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2884
                                      in
                                   [uu____2875]  in
                                 FStar_Syntax_Util.mk_app y uu____2864  in
                               mk_rel1 b uu____2821 uu____2861  in
                             FStar_Syntax_Util.mk_imp uu____2809 uu____2818
                              in
                           let uu____2901 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2901)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2904);
                                      FStar_Syntax_Syntax.pos = uu____2905;
                                      FStar_Syntax_Syntax.vars = uu____2906;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2950 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2950
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2960 =
                              let uu____2963 =
                                let uu____2974 =
                                  let uu____2983 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2983  in
                                [uu____2974]  in
                              FStar_Syntax_Util.mk_app x uu____2963  in
                            let uu____3000 =
                              let uu____3003 =
                                let uu____3014 =
                                  let uu____3023 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____3023  in
                                [uu____3014]  in
                              FStar_Syntax_Util.mk_app y uu____3003  in
                            mk_rel1 b uu____2960 uu____3000  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____3047 =
                               let uu____3050 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____3053 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____3050 uu____3053  in
                             let uu____3056 =
                               let uu____3059 =
                                 let uu____3062 =
                                   let uu____3073 =
                                     let uu____3082 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3082
                                      in
                                   [uu____3073]  in
                                 FStar_Syntax_Util.mk_app x uu____3062  in
                               let uu____3099 =
                                 let uu____3102 =
                                   let uu____3113 =
                                     let uu____3122 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3122
                                      in
                                   [uu____3113]  in
                                 FStar_Syntax_Util.mk_app y uu____3102  in
                               mk_rel1 b uu____3059 uu____3099  in
                             FStar_Syntax_Util.mk_imp uu____3047 uu____3056
                              in
                           let uu____3139 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3139)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___364_3178 = t1  in
                          let uu____3179 =
                            let uu____3180 =
                              let uu____3195 =
                                let uu____3198 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3198  in
                              ([binder], uu____3195)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3180  in
                          {
                            FStar_Syntax_Syntax.n = uu____3179;
                            FStar_Syntax_Syntax.pos =
                              (uu___364_3178.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___364_3178.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3221 ->
                        failwith "unhandled arrow"
                    | uu____3239 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____3276 =
                        let uu____3277 = FStar_Syntax_Subst.compress t1  in
                        uu____3277.FStar_Syntax_Syntax.n  in
                      match uu____3276 with
                      | FStar_Syntax_Syntax.Tm_type uu____3280 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3307 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3307
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3328 =
                                let uu____3329 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3329 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3328
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3359 =
                            let uu____3370 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3388  ->
                                     match uu____3388 with
                                     | (t2,q) ->
                                         let uu____3408 = project i x  in
                                         let uu____3411 = project i y  in
                                         mk_stronger t2 uu____3408 uu____3411)
                                args
                               in
                            match uu____3370 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3359 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3465);
                                      FStar_Syntax_Syntax.pos = uu____3466;
                                      FStar_Syntax_Syntax.vars = uu____3467;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3511  ->
                                   match uu____3511 with
                                   | (bv,q) ->
                                       let uu____3525 =
                                         let uu____3527 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3527  in
                                       FStar_Syntax_Syntax.gen_bv uu____3525
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3536 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3536) bvs
                             in
                          let body =
                            let uu____3538 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3541 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3538 uu____3541  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3550);
                                      FStar_Syntax_Syntax.pos = uu____3551;
                                      FStar_Syntax_Syntax.vars = uu____3552;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3596  ->
                                   match uu____3596 with
                                   | (bv,q) ->
                                       let uu____3610 =
                                         let uu____3612 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3612  in
                                       FStar_Syntax_Syntax.gen_bv uu____3610
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3621 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3621) bvs
                             in
                          let body =
                            let uu____3623 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3626 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3623 uu____3626  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3633 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3636 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3639 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3642 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3636 uu____3639 uu____3642  in
                    let uu____3645 =
                      let uu____3646 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3646  in
                    FStar_Syntax_Util.abs uu____3645 body ret_tot_type  in
                  let stronger1 =
                    let uu____3688 = mk_lid "stronger"  in
                    register env1 uu____3688 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let mrelation_from_interp interp =
                    let repr_a =
                      let uu____3702 =
                        let uu____3713 =
                          let uu____3722 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3722  in
                        [uu____3713]  in
                      FStar_Syntax_Util.mk_app
                        (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                        uu____3702
                       in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        (FStar_Pervasives_Native.Some
                           (interp.FStar_Syntax_Syntax.pos)) repr_a
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        (FStar_Pervasives_Native.Some
                           (interp.FStar_Syntax_Syntax.pos)) wp_a1
                       in
                    let body =
                      let uu____3746 =
                        let uu____3757 =
                          let uu____3766 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3766  in
                        let uu____3767 =
                          let uu____3778 =
                            let uu____3787 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            FStar_Syntax_Syntax.as_arg uu____3787  in
                          let uu____3788 =
                            let uu____3799 =
                              let uu____3808 =
                                let uu____3809 =
                                  let uu____3820 =
                                    let uu____3829 =
                                      FStar_Syntax_Syntax.bv_to_name a1  in
                                    FStar_Syntax_Syntax.iarg uu____3829  in
                                  let uu____3830 =
                                    let uu____3841 =
                                      let uu____3850 =
                                        FStar_Syntax_Syntax.bv_to_name c  in
                                      FStar_Syntax_Syntax.as_arg uu____3850
                                       in
                                    [uu____3841]  in
                                  uu____3820 :: uu____3830  in
                                FStar_Syntax_Util.mk_app interp uu____3809
                                 in
                              FStar_Syntax_Syntax.as_arg uu____3808  in
                            [uu____3799]  in
                          uu____3778 :: uu____3788  in
                        uu____3757 :: uu____3767  in
                      FStar_Syntax_Util.mk_app stronger2 uu____3746  in
                    let abs1 =
                      let uu____3910 =
                        let uu____3911 =
                          let uu____3920 =
                            FStar_Syntax_Syntax.mk_implicit_binder a1  in
                          let uu____3927 =
                            let uu____3936 = FStar_Syntax_Syntax.mk_binder c
                               in
                            let uu____3943 =
                              let uu____3952 =
                                FStar_Syntax_Syntax.mk_binder wp  in
                              [uu____3952]  in
                            uu____3936 :: uu____3943  in
                          uu____3920 :: uu____3927  in
                        FStar_List.append binders uu____3911  in
                      FStar_Syntax_Util.abs uu____3910 body ret_tot_type  in
                    abs1  in
                  let mrelation =
                    match ((ed.FStar_Syntax_Syntax.interp),
                            (ed.FStar_Syntax_Syntax.mrelation))
                    with
                    | (uu____3998,FStar_Pervasives_Native.Some t) ->
                        FStar_Pervasives_Native.Some
                          (FStar_Pervasives_Native.snd t)
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        FStar_Pervasives_Native.None
                    | (FStar_Pervasives_Native.Some
                       i,FStar_Pervasives_Native.None ) ->
                        let uu____4019 =
                          mrelation_from_interp
                            (FStar_Pervasives_Native.snd i)
                           in
                        FStar_Pervasives_Native.Some uu____4019
                     in
                  let mrelation1 =
                    let uu____4029 =
                      let uu____4036 = mk_lid "mrelation"  in
                      register env1 uu____4036  in
                    FStar_Util.map_opt mrelation uu____4029  in
                  let mrelation2 =
                    FStar_Util.map_opt mrelation1 mk_generic_app  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____4048 = FStar_Util.prefix gamma  in
                    match uu____4048 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____4114 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____4114
                             in
                          let uu____4119 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____4119 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____4129 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____4129  in
                              let guard_free1 =
                                let uu____4141 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____4141  in
                              let pat =
                                let uu____4145 =
                                  let uu____4156 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____4156]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____4145
                                 in
                              let pattern_guarded_body =
                                let uu____4184 =
                                  let uu____4185 =
                                    let uu____4192 =
                                      let uu____4193 =
                                        let uu____4206 =
                                          let uu____4217 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____4217]  in
                                        [uu____4206]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____4193
                                       in
                                    (body, uu____4192)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____4185  in
                                mk1 uu____4184  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____4264 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____4273 =
                            let uu____4276 =
                              let uu____4277 =
                                let uu____4280 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____4283 =
                                  let uu____4294 = args_of_binders1 wp_args
                                     in
                                  let uu____4297 =
                                    let uu____4300 =
                                      let uu____4301 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____4301
                                       in
                                    [uu____4300]  in
                                  FStar_List.append uu____4294 uu____4297  in
                                FStar_Syntax_Util.mk_app uu____4280
                                  uu____4283
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____4277  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____4276
                             in
                          FStar_Syntax_Util.abs gamma uu____4273
                            ret_gtot_type
                           in
                        let uu____4302 =
                          let uu____4303 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____4303  in
                        FStar_Syntax_Util.abs uu____4302 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____4319 = mk_lid "ite_wp"  in
                    register env1 uu____4319 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____4327 = FStar_Util.prefix gamma  in
                    match uu____4327 with
                    | (wp_args,post) ->
                        let uu____4382 =
                          FStar_Syntax_Util.arrow_formals_comp
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        (match uu____4382 with
                         | (bs,uu____4398) ->
                             let bs1 =
                               FStar_List.map
                                 FStar_Syntax_Syntax.freshen_binder bs
                                in
                             let args =
                               FStar_List.map
                                 (fun uu____4461  ->
                                    match uu____4461 with
                                    | (bv,q) ->
                                        let uu____4480 =
                                          FStar_Syntax_Syntax.bv_to_name bv
                                           in
                                        (uu____4480, q)) bs1
                                in
                             let body =
                               let uu____4484 =
                                 let uu____4485 =
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.bv_to_name
                                     (FStar_Pervasives_Native.fst post)
                                    in
                                 FStar_Syntax_Util.mk_app uu____4485 args  in
                               FStar_Syntax_Util.close_forall_no_univs bs1
                                 uu____4484
                                in
                             let uu____4492 =
                               let uu____4493 =
                                 let uu____4502 =
                                   FStar_Syntax_Syntax.binders_of_list [a1]
                                    in
                                 FStar_List.append uu____4502 gamma  in
                               FStar_List.append binders uu____4493  in
                             FStar_Syntax_Util.abs uu____4492 body
                               ret_gtot_type)
                     in
                  let null_wp1 =
                    let uu____4524 = mk_lid "null_wp"  in
                    register env1 uu____4524 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4537 =
                        let uu____4548 =
                          let uu____4551 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4552 =
                            let uu____4555 =
                              let uu____4556 =
                                let uu____4567 =
                                  let uu____4576 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4576  in
                                [uu____4567]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4556
                               in
                            let uu____4593 =
                              let uu____4596 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4596]  in
                            uu____4555 :: uu____4593  in
                          uu____4551 :: uu____4552  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4548
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4537  in
                    let uu____4605 =
                      let uu____4606 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4606  in
                    FStar_Syntax_Util.abs uu____4605 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4622 = mk_lid "wp_trivial"  in
                    register env1 uu____4622 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4628 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4628
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4640 =
                      let uu____4641 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4641  in
                    let uu____4689 =
                      let uu___365_4690 = ed  in
                      let uu____4691 =
                        let uu____4692 = c wp_if_then_else2  in
                        ([], uu____4692)  in
                      let uu____4699 =
                        let uu____4700 = c ite_wp2  in ([], uu____4700)  in
                      let uu____4707 =
                        let uu____4708 = c stronger2  in ([], uu____4708)  in
                      let uu____4715 =
                        let uu____4716 = c wp_close2  in ([], uu____4716)  in
                      let uu____4723 =
                        let uu____4724 = c wp_assert2  in ([], uu____4724)
                         in
                      let uu____4731 =
                        let uu____4732 = c wp_assume2  in ([], uu____4732)
                         in
                      let uu____4739 =
                        let uu____4740 = c null_wp2  in ([], uu____4740)  in
                      let uu____4747 =
                        let uu____4748 = c wp_trivial2  in ([], uu____4748)
                         in
                      let uu____4755 =
                        FStar_Util.map_opt mrelation2
                          (fun t  ->
                             let uu____4767 = c t  in ([], uu____4767))
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___365_4690.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___365_4690.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___365_4690.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___365_4690.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.spec =
                          (uu___365_4690.FStar_Syntax_Syntax.spec);
                        FStar_Syntax_Syntax.signature =
                          (uu___365_4690.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.if_then_else = uu____4691;
                        FStar_Syntax_Syntax.ite_wp = uu____4699;
                        FStar_Syntax_Syntax.stronger = uu____4707;
                        FStar_Syntax_Syntax.close_wp = uu____4715;
                        FStar_Syntax_Syntax.assert_p = uu____4723;
                        FStar_Syntax_Syntax.assume_p = uu____4731;
                        FStar_Syntax_Syntax.null_wp = uu____4739;
                        FStar_Syntax_Syntax.trivial = uu____4747;
                        FStar_Syntax_Syntax.repr =
                          (uu___365_4690.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.elaborated =
                          (uu___365_4690.FStar_Syntax_Syntax.elaborated);
                        FStar_Syntax_Syntax.spec_dm4f =
                          (uu___365_4690.FStar_Syntax_Syntax.spec_dm4f);
                        FStar_Syntax_Syntax.interp =
                          (uu___365_4690.FStar_Syntax_Syntax.interp);
                        FStar_Syntax_Syntax.mrelation = uu____4755;
                        FStar_Syntax_Syntax.actions =
                          (uu___365_4690.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___365_4690.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4640, uu____4689)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___366_4787 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___366_4787.subst);
        tc_const = (uu___366_4787.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4808 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4828 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4849) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___352_4863  ->
                match uu___352_4863 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4866 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4868 ->
        let uu____4869 =
          let uu____4875 =
            let uu____4877 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4877
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4875)  in
        FStar_Errors.raise_error uu____4869 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___353_4887  ->
    match uu___353_4887 with
    | N t ->
        let uu____4890 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4890
    | M t ->
        let uu____4894 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4894
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4903,c) -> nm_of_comp c
    | uu____4925 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4938 = nm_of_comp c  in
    match uu____4938 with | M uu____4940 -> true | N uu____4942 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4953 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4969 =
        let uu____4978 =
          let uu____4985 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4985  in
        [uu____4978]  in
      let uu____5004 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4969 uu____5004  in
    let uu____5007 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____5007
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____5049 =
          let uu____5050 =
            let uu____5065 =
              let uu____5074 =
                let uu____5081 =
                  let uu____5082 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____5082  in
                let uu____5083 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____5081, uu____5083)  in
              [uu____5074]  in
            let uu____5101 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____5065, uu____5101)  in
          FStar_Syntax_Syntax.Tm_arrow uu____5050  in
        mk1 uu____5049

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5141) ->
          let binders1 =
            FStar_List.map
              (fun uu____5187  ->
                 match uu____5187 with
                 | (bv,aqual) ->
                     let uu____5206 =
                       let uu___367_5207 = bv  in
                       let uu____5208 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___367_5207.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___367_5207.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____5208
                       }  in
                     (uu____5206, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____5213,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____5215);
                             FStar_Syntax_Syntax.pos = uu____5216;
                             FStar_Syntax_Syntax.vars = uu____5217;_})
               ->
               let uu____5246 =
                 let uu____5247 =
                   let uu____5262 =
                     let uu____5265 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____5265  in
                   (binders1, uu____5262)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____5247  in
               mk1 uu____5246
           | uu____5276 ->
               let uu____5277 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____5277 with
                | N hn ->
                    let uu____5279 =
                      let uu____5280 =
                        let uu____5295 =
                          let uu____5298 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____5298  in
                        (binders1, uu____5295)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____5280  in
                    mk1 uu____5279
                | M a ->
                    let uu____5310 =
                      let uu____5311 =
                        let uu____5326 =
                          let uu____5335 =
                            let uu____5344 =
                              let uu____5351 =
                                let uu____5352 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____5352  in
                              let uu____5353 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____5351, uu____5353)  in
                            [uu____5344]  in
                          FStar_List.append binders1 uu____5335  in
                        let uu____5377 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____5326, uu____5377)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____5311  in
                    mk1 uu____5310))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5471 = f x  in
                    FStar_Util.string_builder_append strb uu____5471);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5480 = f x1  in
                         FStar_Util.string_builder_append strb uu____5480))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5484 =
              let uu____5490 =
                let uu____5492 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5494 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5492 uu____5494
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5490)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5484  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5516 =
              let uu____5517 = FStar_Syntax_Subst.compress ty  in
              uu____5517.FStar_Syntax_Syntax.n  in
            match uu____5516 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5543 =
                  let uu____5545 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5545  in
                if uu____5543
                then false
                else
                  (try
                     (fun uu___369_5562  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5586 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5586 s  in
                              let uu____5589 =
                                let uu____5591 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5591  in
                              if uu____5589
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5597 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5597 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5622  ->
                                          match uu____5622 with
                                          | (bv,uu____5634) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n1 - (FStar_List.length binders1)
                                      in
                                   if k > (Prims.parse_int "0")
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____5662 ->
                ((let uu____5664 =
                    let uu____5670 =
                      let uu____5672 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5672
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5670)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5664);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5688 =
              let uu____5689 = FStar_Syntax_Subst.compress head2  in
              uu____5689.FStar_Syntax_Syntax.n  in
            match uu____5688 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____5695 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5695)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5698 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5698 with
                 | ((uu____5708,ty),uu____5710) ->
                     let uu____5715 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5715
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5728 =
                         let uu____5729 = FStar_Syntax_Subst.compress res  in
                         uu____5729.FStar_Syntax_Syntax.n  in
                       (match uu____5728 with
                        | FStar_Syntax_Syntax.Tm_app uu____5733 -> true
                        | uu____5751 ->
                            ((let uu____5753 =
                                let uu____5759 =
                                  let uu____5761 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5761
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5759)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5753);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5769 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5771 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5774) ->
                is_valid_application t2
            | uu____5779 -> false  in
          let uu____5781 = is_valid_application head1  in
          if uu____5781
          then
            let uu____5784 =
              let uu____5785 =
                let uu____5802 =
                  FStar_List.map
                    (fun uu____5831  ->
                       match uu____5831 with
                       | (t2,qual) ->
                           let uu____5856 = star_type' env t2  in
                           (uu____5856, qual)) args
                   in
                (head1, uu____5802)  in
              FStar_Syntax_Syntax.Tm_app uu____5785  in
            mk1 uu____5784
          else
            (let uu____5873 =
               let uu____5879 =
                 let uu____5881 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5881
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5879)  in
             FStar_Errors.raise_err uu____5873)
      | FStar_Syntax_Syntax.Tm_bvar uu____5885 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5886 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5887 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5888 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5916 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5916 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___370_5924 = env  in
                 let uu____5925 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5925;
                   subst = (uu___370_5924.subst);
                   tc_const = (uu___370_5924.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___371_5952 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___371_5952.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___371_5952.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5959 =
            let uu____5960 =
              let uu____5967 = star_type' env t2  in (uu____5967, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5960  in
          mk1 uu____5959
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____6019 =
            let uu____6020 =
              let uu____6047 = star_type' env e  in
              let uu____6050 =
                let uu____6067 =
                  let uu____6076 = star_type' env t2  in
                  FStar_Util.Inl uu____6076  in
                (uu____6067, FStar_Pervasives_Native.None)  in
              (uu____6047, uu____6050, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____6020  in
          mk1 uu____6019
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____6164 =
            let uu____6165 =
              let uu____6192 = star_type' env e  in
              let uu____6195 =
                let uu____6212 =
                  let uu____6221 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____6221  in
                (uu____6212, FStar_Pervasives_Native.None)  in
              (uu____6192, uu____6195, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____6165  in
          mk1 uu____6164
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____6262,(uu____6263,FStar_Pervasives_Native.Some uu____6264),uu____6265)
          ->
          let uu____6314 =
            let uu____6320 =
              let uu____6322 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____6322
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6320)  in
          FStar_Errors.raise_err uu____6314
      | FStar_Syntax_Syntax.Tm_refine uu____6326 ->
          let uu____6333 =
            let uu____6339 =
              let uu____6341 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____6341
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6339)  in
          FStar_Errors.raise_err uu____6333
      | FStar_Syntax_Syntax.Tm_uinst uu____6345 ->
          let uu____6352 =
            let uu____6358 =
              let uu____6360 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____6360
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6358)  in
          FStar_Errors.raise_err uu____6352
      | FStar_Syntax_Syntax.Tm_quoted uu____6364 ->
          let uu____6371 =
            let uu____6377 =
              let uu____6379 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____6379
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6377)  in
          FStar_Errors.raise_err uu____6371
      | FStar_Syntax_Syntax.Tm_constant uu____6383 ->
          let uu____6384 =
            let uu____6390 =
              let uu____6392 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____6392
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6390)  in
          FStar_Errors.raise_err uu____6384
      | FStar_Syntax_Syntax.Tm_match uu____6396 ->
          let uu____6419 =
            let uu____6425 =
              let uu____6427 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____6427
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6425)  in
          FStar_Errors.raise_err uu____6419
      | FStar_Syntax_Syntax.Tm_let uu____6431 ->
          let uu____6445 =
            let uu____6451 =
              let uu____6453 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____6453
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6451)  in
          FStar_Errors.raise_err uu____6445
      | FStar_Syntax_Syntax.Tm_uvar uu____6457 ->
          let uu____6470 =
            let uu____6476 =
              let uu____6478 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6478
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6476)  in
          FStar_Errors.raise_err uu____6470
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6482 =
            let uu____6488 =
              let uu____6490 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6490
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6488)  in
          FStar_Errors.raise_err uu____6482
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6495 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6495
      | FStar_Syntax_Syntax.Tm_delayed uu____6498 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___355_6530  ->
    match uu___355_6530 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___354_6541  ->
                match uu___354_6541 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6544 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6554 =
      let uu____6555 = FStar_Syntax_Subst.compress t  in
      uu____6555.FStar_Syntax_Syntax.n  in
    match uu____6554 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6587 =
            let uu____6588 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6588  in
          is_C uu____6587  in
        if r
        then
          ((let uu____6612 =
              let uu____6614 =
                FStar_List.for_all
                  (fun uu____6625  ->
                     match uu____6625 with | (h,uu____6634) -> is_C h) args
                 in
              Prims.op_Negation uu____6614  in
            if uu____6612 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6647 =
              let uu____6649 =
                FStar_List.for_all
                  (fun uu____6661  ->
                     match uu____6661 with
                     | (h,uu____6670) ->
                         let uu____6675 = is_C h  in
                         Prims.op_Negation uu____6675) args
                 in
              Prims.op_Negation uu____6649  in
            if uu____6647 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6704 = nm_of_comp comp  in
        (match uu____6704 with
         | M t1 ->
             ((let uu____6708 = is_C t1  in
               if uu____6708 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6717) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6723) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6729,uu____6730) -> is_C t1
    | uu____6771 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____6807 =
            let uu____6808 =
              let uu____6825 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6828 =
                let uu____6839 =
                  let uu____6848 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6848)  in
                [uu____6839]  in
              (uu____6825, uu____6828)  in
            FStar_Syntax_Syntax.Tm_app uu____6808  in
          mk1 uu____6807  in
        let uu____6884 =
          let uu____6885 = FStar_Syntax_Syntax.mk_binder p  in [uu____6885]
           in
        FStar_Syntax_Util.abs uu____6884 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___356_6910  ->
    match uu___356_6910 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6913 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____7151 =
          match uu____7151 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____7188 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____7191 =
                       let uu____7193 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____7193  in
                     Prims.op_Negation uu____7191)
                   in
                if uu____7188
                then
                  let uu____7195 =
                    let uu____7201 =
                      let uu____7203 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____7205 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____7207 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____7203 uu____7205 uu____7207
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____7201)  in
                  FStar_Errors.raise_err uu____7195
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____7232 = mk_return env t1 s_e  in
                     ((M t1), uu____7232, u_e)))
               | (M t1,N t2) ->
                   let uu____7239 =
                     let uu____7245 =
                       let uu____7247 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7249 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7251 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____7247 uu____7249 uu____7251
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____7245)
                      in
                   FStar_Errors.raise_err uu____7239)
           in
        let ensure_m env1 e2 =
          let strip_m uu___357_7303 =
            match uu___357_7303 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____7319 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____7340 =
                let uu____7346 =
                  let uu____7348 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____7348
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____7346)  in
              FStar_Errors.raise_error uu____7340 e2.FStar_Syntax_Syntax.pos
          | M uu____7358 ->
              let uu____7359 = check env1 e2 context_nm  in
              strip_m uu____7359
           in
        let uu____7366 =
          let uu____7367 = FStar_Syntax_Subst.compress e  in
          uu____7367.FStar_Syntax_Syntax.n  in
        match uu____7366 with
        | FStar_Syntax_Syntax.Tm_bvar uu____7376 ->
            let uu____7377 = infer env e  in return_if uu____7377
        | FStar_Syntax_Syntax.Tm_name uu____7384 ->
            let uu____7385 = infer env e  in return_if uu____7385
        | FStar_Syntax_Syntax.Tm_fvar uu____7392 ->
            let uu____7393 = infer env e  in return_if uu____7393
        | FStar_Syntax_Syntax.Tm_abs uu____7400 ->
            let uu____7419 = infer env e  in return_if uu____7419
        | FStar_Syntax_Syntax.Tm_constant uu____7426 ->
            let uu____7427 = infer env e  in return_if uu____7427
        | FStar_Syntax_Syntax.Tm_quoted uu____7434 ->
            let uu____7441 = infer env e  in return_if uu____7441
        | FStar_Syntax_Syntax.Tm_app uu____7448 ->
            let uu____7465 = infer env e  in return_if uu____7465
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7473 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7473 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7538) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7544) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7550,uu____7551) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7592 ->
            let uu____7606 =
              let uu____7608 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7608  in
            failwith uu____7606
        | FStar_Syntax_Syntax.Tm_type uu____7617 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7625 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7647 ->
            let uu____7654 =
              let uu____7656 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7656  in
            failwith uu____7654
        | FStar_Syntax_Syntax.Tm_uvar uu____7665 ->
            let uu____7678 =
              let uu____7680 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7680  in
            failwith uu____7678
        | FStar_Syntax_Syntax.Tm_delayed uu____7689 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7719 =
              let uu____7721 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7721  in
            failwith uu____7719

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____7751 =
        let uu____7752 = FStar_Syntax_Subst.compress e  in
        uu____7752.FStar_Syntax_Syntax.n  in
      match uu____7751 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7771 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7771
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7822;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7823;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7829 =
                  let uu___372_7830 = rc  in
                  let uu____7831 =
                    let uu____7836 =
                      let uu____7839 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7839  in
                    FStar_Pervasives_Native.Some uu____7836  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___372_7830.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7831;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___372_7830.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7829
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___373_7851 = env  in
            let uu____7852 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7852;
              subst = (uu___373_7851.subst);
              tc_const = (uu___373_7851.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7878  ->
                 match uu____7878 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___374_7901 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___374_7901.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___374_7901.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7902 =
            FStar_List.fold_left
              (fun uu____7933  ->
                 fun uu____7934  ->
                   match (uu____7933, uu____7934) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7992 = is_C c  in
                       if uu____7992
                       then
                         let xw =
                           let uu____8002 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____8002
                            in
                         let x =
                           let uu___375_8005 = bv  in
                           let uu____8006 =
                             let uu____8009 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____8009  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___375_8005.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___375_8005.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____8006
                           }  in
                         let env3 =
                           let uu___376_8011 = env2  in
                           let uu____8012 =
                             let uu____8015 =
                               let uu____8016 =
                                 let uu____8023 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____8023)  in
                               FStar_Syntax_Syntax.NT uu____8016  in
                             uu____8015 :: (env2.subst)  in
                           {
                             tcenv = (uu___376_8011.tcenv);
                             subst = uu____8012;
                             tc_const = (uu___376_8011.tc_const)
                           }  in
                         let uu____8028 =
                           let uu____8031 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____8032 =
                             let uu____8035 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____8035 :: acc  in
                           uu____8031 :: uu____8032  in
                         (env3, uu____8028)
                       else
                         (let x =
                            let uu___377_8041 = bv  in
                            let uu____8042 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___377_8041.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___377_8041.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____8042
                            }  in
                          let uu____8045 =
                            let uu____8048 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____8048 :: acc  in
                          (env2, uu____8045))) (env1, []) binders1
             in
          (match uu____7902 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____8068 =
                 let check_what =
                   let uu____8094 = is_monadic rc_opt1  in
                   if uu____8094 then check_m else check_n  in
                 let uu____8111 = check_what env2 body1  in
                 match uu____8111 with
                 | (t,s_body,u_body) ->
                     let uu____8131 =
                       let uu____8134 =
                         let uu____8135 = is_monadic rc_opt1  in
                         if uu____8135 then M t else N t  in
                       comp_of_nm uu____8134  in
                     (uu____8131, s_body, u_body)
                  in
               (match uu____8068 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____8175 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___358_8181  ->
                                           match uu___358_8181 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____8184 -> false))
                                    in
                                 if uu____8175
                                 then
                                   let uu____8187 =
                                     FStar_List.filter
                                       (fun uu___359_8191  ->
                                          match uu___359_8191 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____8194 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____8187
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____8205 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___360_8211  ->
                                         match uu___360_8211 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____8214 -> false))
                                  in
                               if uu____8205
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___361_8223  ->
                                        match uu___361_8223 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____8226 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____8228 =
                                   let uu____8229 =
                                     let uu____8234 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____8234
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____8229 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____8228
                               else
                                 (let uu____8241 =
                                    let uu___378_8242 = rc  in
                                    let uu____8243 =
                                      let uu____8248 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____8248
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___378_8242.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____8243;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___378_8242.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____8241))
                       in
                    let uu____8253 =
                      let comp1 =
                        let uu____8261 = is_monadic rc_opt1  in
                        let uu____8263 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____8261 uu____8263
                         in
                      let uu____8264 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____8264,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____8253 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____8302 =
                             let uu____8303 =
                               let uu____8322 =
                                 let uu____8325 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____8325 s_rc_opt  in
                               (s_binders1, s_body1, uu____8322)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8303  in
                           mk1 uu____8302  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____8345 =
                             let uu____8346 =
                               let uu____8365 =
                                 let uu____8368 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____8368 u_rc_opt  in
                               (u_binders2, u_body2, uu____8365)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8346  in
                           mk1 uu____8345  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____8384;_};
            FStar_Syntax_Syntax.fv_delta = uu____8385;
            FStar_Syntax_Syntax.fv_qual = uu____8386;_}
          ->
          let uu____8389 =
            let uu____8394 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8394  in
          (match uu____8389 with
           | (uu____8425,t) ->
               let uu____8427 =
                 let uu____8428 = normalize1 t  in N uu____8428  in
               (uu____8427, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8429;
             FStar_Syntax_Syntax.vars = uu____8430;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8509 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8509 with
           | (unary_op1,uu____8533) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8604;
             FStar_Syntax_Syntax.vars = uu____8605;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8701 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8701 with
           | (unary_op1,uu____8725) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8804;
             FStar_Syntax_Syntax.vars = uu____8805;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8843 = infer env a  in
          (match uu____8843 with
           | (t,s,u) ->
               let uu____8859 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8859 with
                | (head1,uu____8883) ->
                    let uu____8908 =
                      let uu____8909 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8909  in
                    let uu____8910 =
                      let uu____8911 =
                        let uu____8912 =
                          let uu____8929 =
                            let uu____8940 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8940]  in
                          (head1, uu____8929)  in
                        FStar_Syntax_Syntax.Tm_app uu____8912  in
                      mk1 uu____8911  in
                    let uu____8977 =
                      let uu____8978 =
                        let uu____8979 =
                          let uu____8996 =
                            let uu____9007 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____9007]  in
                          (head1, uu____8996)  in
                        FStar_Syntax_Syntax.Tm_app uu____8979  in
                      mk1 uu____8978  in
                    (uu____8908, uu____8910, uu____8977)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____9044;
             FStar_Syntax_Syntax.vars = uu____9045;_},(a1,uu____9047)::a2::[])
          ->
          let uu____9103 = infer env a1  in
          (match uu____9103 with
           | (t,s,u) ->
               let uu____9119 = FStar_Syntax_Util.head_and_args e  in
               (match uu____9119 with
                | (head1,uu____9143) ->
                    let uu____9168 =
                      let uu____9169 =
                        let uu____9170 =
                          let uu____9187 =
                            let uu____9198 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____9198; a2]  in
                          (head1, uu____9187)  in
                        FStar_Syntax_Syntax.Tm_app uu____9170  in
                      mk1 uu____9169  in
                    let uu____9243 =
                      let uu____9244 =
                        let uu____9245 =
                          let uu____9262 =
                            let uu____9273 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____9273; a2]  in
                          (head1, uu____9262)  in
                        FStar_Syntax_Syntax.Tm_app uu____9245  in
                      mk1 uu____9244  in
                    (t, uu____9168, uu____9243)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____9318;
             FStar_Syntax_Syntax.vars = uu____9319;_},uu____9320)
          ->
          let uu____9345 =
            let uu____9351 =
              let uu____9353 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9353
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9351)  in
          FStar_Errors.raise_error uu____9345 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____9363;
             FStar_Syntax_Syntax.vars = uu____9364;_},uu____9365)
          ->
          let uu____9390 =
            let uu____9396 =
              let uu____9398 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9398
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9396)  in
          FStar_Errors.raise_error uu____9390 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____9434 = check_n env head1  in
          (match uu____9434 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____9457 =
                   let uu____9458 = FStar_Syntax_Subst.compress t  in
                   uu____9458.FStar_Syntax_Syntax.n  in
                 match uu____9457 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9462 -> true
                 | uu____9478 -> false  in
               let rec flatten1 t =
                 let uu____9500 =
                   let uu____9501 = FStar_Syntax_Subst.compress t  in
                   uu____9501.FStar_Syntax_Syntax.n  in
                 match uu____9500 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9520);
                                FStar_Syntax_Syntax.pos = uu____9521;
                                FStar_Syntax_Syntax.vars = uu____9522;_})
                     when is_arrow t1 ->
                     let uu____9551 = flatten1 t1  in
                     (match uu____9551 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9651,uu____9652)
                     -> flatten1 e1
                 | uu____9693 ->
                     let uu____9694 =
                       let uu____9700 =
                         let uu____9702 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9702
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9700)  in
                     FStar_Errors.raise_err uu____9694
                  in
               let uu____9720 = flatten1 t_head  in
               (match uu____9720 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9795 =
                          let uu____9801 =
                            let uu____9803 = FStar_Util.string_of_int n1  in
                            let uu____9811 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9823 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9803 uu____9811 uu____9823
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9801)
                           in
                        FStar_Errors.raise_err uu____9795)
                     else ();
                     (let uu____9835 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9835 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9888 args1 =
                            match uu____9888 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9988 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9988
                                 | (binders3,[]) ->
                                     let uu____10026 =
                                       let uu____10027 =
                                         let uu____10030 =
                                           let uu____10031 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____10031
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____10030
                                          in
                                       uu____10027.FStar_Syntax_Syntax.n  in
                                     (match uu____10026 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____10064 =
                                            let uu____10065 =
                                              let uu____10066 =
                                                let uu____10081 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____10081)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____10066
                                               in
                                            mk1 uu____10065  in
                                          N uu____10064
                                      | uu____10094 -> failwith "wat?")
                                 | ([],uu____10096::uu____10097) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____10150)::binders3,(arg,uu____10153)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____10240 = FStar_List.splitAt n' binders1
                             in
                          (match uu____10240 with
                           | (binders2,uu____10278) ->
                               let uu____10311 =
                                 let uu____10334 =
                                   FStar_List.map2
                                     (fun uu____10396  ->
                                        fun uu____10397  ->
                                          match (uu____10396, uu____10397)
                                          with
                                          | ((bv,uu____10445),(arg,q)) ->
                                              let uu____10474 =
                                                let uu____10475 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____10475.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____10474 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10496 ->
                                                   let uu____10497 =
                                                     let uu____10504 =
                                                       star_type' env arg  in
                                                     (uu____10504, q)  in
                                                   (uu____10497, [(arg, q)])
                                               | uu____10541 ->
                                                   let uu____10542 =
                                                     check_n env arg  in
                                                   (match uu____10542 with
                                                    | (uu____10567,s_arg,u_arg)
                                                        ->
                                                        let uu____10570 =
                                                          let uu____10579 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10579
                                                          then
                                                            let uu____10590 =
                                                              let uu____10597
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10597,
                                                                q)
                                                               in
                                                            [uu____10590;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10570))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____10334  in
                               (match uu____10311 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10725 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10738 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10725, uu____10738)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10807) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10813) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10819,uu____10820) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10862 =
            let uu____10863 = env.tc_const c  in N uu____10863  in
          (uu____10862, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10870 ->
          let uu____10884 =
            let uu____10886 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10886  in
          failwith uu____10884
      | FStar_Syntax_Syntax.Tm_type uu____10895 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10903 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10925 ->
          let uu____10932 =
            let uu____10934 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10934  in
          failwith uu____10932
      | FStar_Syntax_Syntax.Tm_uvar uu____10943 ->
          let uu____10956 =
            let uu____10958 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10958  in
          failwith uu____10956
      | FStar_Syntax_Syntax.Tm_delayed uu____10967 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10997 =
            let uu____10999 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10999  in
          failwith uu____10997

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____11048 = check_n env e0  in
          match uu____11048 with
          | (uu____11061,s_e0,u_e0) ->
              let uu____11064 =
                let uu____11093 =
                  FStar_List.map
                    (fun b  ->
                       let uu____11154 = FStar_Syntax_Subst.open_branch b  in
                       match uu____11154 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___379_11196 = env  in
                             let uu____11197 =
                               let uu____11198 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____11198
                                in
                             {
                               tcenv = uu____11197;
                               subst = (uu___379_11196.subst);
                               tc_const = (uu___379_11196.tc_const)
                             }  in
                           let uu____11201 = f env1 body  in
                           (match uu____11201 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____11273 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____11093  in
              (match uu____11064 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____11379 = FStar_List.hd nms  in
                     match uu____11379 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___362_11388  ->
                          match uu___362_11388 with
                          | M uu____11390 -> true
                          | uu____11392 -> false) nms
                      in
                   let uu____11394 =
                     let uu____11431 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11521  ->
                              match uu____11521 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11705 =
                                         check env original_body (M t2)  in
                                       (match uu____11705 with
                                        | (uu____11742,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11781,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____11431  in
                   (match uu____11394 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____11970  ->
                                 match uu____11970 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____12021 =
                                         let uu____12022 =
                                           let uu____12039 =
                                             let uu____12050 =
                                               let uu____12059 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____12062 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____12059, uu____12062)  in
                                             [uu____12050]  in
                                           (s_body, uu____12039)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____12022
                                          in
                                       mk1 uu____12021  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____12197 =
                              let uu____12198 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12198]  in
                            let uu____12217 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____12197 uu____12217
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____12241 =
                              let uu____12250 =
                                let uu____12257 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____12257
                                 in
                              [uu____12250]  in
                            let uu____12276 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____12241 uu____12276
                             in
                          let uu____12279 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____12318 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____12279, uu____12318)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____12428 =
                             let uu____12429 =
                               let uu____12430 =
                                 let uu____12457 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____12457,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12430
                                in
                             mk1 uu____12429  in
                           let uu____12516 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____12428, uu____12516))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____12581 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12581]  in
            let uu____12600 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12600 with
            | (x_binders1,e21) ->
                let uu____12613 = infer env e1  in
                (match uu____12613 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12630 = is_C t1  in
                       if uu____12630
                       then
                         let uu___380_12633 = binding  in
                         let uu____12634 =
                           let uu____12637 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12637  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___380_12633.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___380_12633.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12634;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___380_12633.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___380_12633.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___380_12633.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___380_12633.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___381_12641 = env  in
                       let uu____12642 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___382_12644 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___382_12644.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___382_12644.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12642;
                         subst = (uu___381_12641.subst);
                         tc_const = (uu___381_12641.tc_const)
                       }  in
                     let uu____12645 = proceed env1 e21  in
                     (match uu____12645 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___383_12662 = binding  in
                            let uu____12663 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___383_12662.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___383_12662.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12663;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___383_12662.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___383_12662.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___383_12662.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___383_12662.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12666 =
                            let uu____12667 =
                              let uu____12668 =
                                let uu____12682 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___384_12699 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___384_12699.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12682)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12668  in
                            mk1 uu____12667  in
                          let uu____12700 =
                            let uu____12701 =
                              let uu____12702 =
                                let uu____12716 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___385_12733 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___385_12733.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12716)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12702  in
                            mk1 uu____12701  in
                          (nm_rec, uu____12666, uu____12700))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___386_12738 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___386_12738.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___386_12738.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___386_12738.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___386_12738.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___386_12738.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___387_12740 = env  in
                       let uu____12741 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___388_12743 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___388_12743.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___388_12743.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12741;
                         subst = (uu___387_12740.subst);
                         tc_const = (uu___387_12740.tc_const)
                       }  in
                     let uu____12744 = ensure_m env1 e21  in
                     (match uu____12744 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12768 =
                              let uu____12769 =
                                let uu____12786 =
                                  let uu____12797 =
                                    let uu____12806 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12809 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12806, uu____12809)  in
                                  [uu____12797]  in
                                (s_e2, uu____12786)  in
                              FStar_Syntax_Syntax.Tm_app uu____12769  in
                            mk1 uu____12768  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12851 =
                              let uu____12852 =
                                let uu____12869 =
                                  let uu____12880 =
                                    let uu____12889 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12889)  in
                                  [uu____12880]  in
                                (s_e1, uu____12869)  in
                              FStar_Syntax_Syntax.Tm_app uu____12852  in
                            mk1 uu____12851  in
                          let uu____12925 =
                            let uu____12926 =
                              let uu____12927 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12927]  in
                            FStar_Syntax_Util.abs uu____12926 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12946 =
                            let uu____12947 =
                              let uu____12948 =
                                let uu____12962 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___389_12979 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___389_12979.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12962)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12948  in
                            mk1 uu____12947  in
                          ((M t2), uu____12925, uu____12946)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12989 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12989  in
      let uu____12990 = check env e mn  in
      match uu____12990 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____13006 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____13029 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____13029  in
      let uu____13030 = check env e mn  in
      match uu____13030 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____13046 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
        FStar_Syntax_Syntax.result_typ = t;
        FStar_Syntax_Syntax.effect_args = [];
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____13079 =
           let uu____13081 = is_C c  in Prims.op_Negation uu____13081  in
         if uu____13079 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____13095 =
           let uu____13096 = FStar_Syntax_Subst.compress c  in
           uu____13096.FStar_Syntax_Syntax.n  in
         match uu____13095 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____13125 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____13125 with
              | (wp_head,wp_args) ->
                  ((let uu____13169 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____13188 =
                           let uu____13190 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____13190
                            in
                         Prims.op_Negation uu____13188)
                       in
                    if uu____13169 then failwith "mismatch" else ());
                   (let uu____13203 =
                      let uu____13204 =
                        let uu____13221 =
                          FStar_List.map2
                            (fun uu____13259  ->
                               fun uu____13260  ->
                                 match (uu____13259, uu____13260) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____13322 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____13322
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____13331 =
                                         let uu____13333 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____13333 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____13331
                                       then
                                         let uu____13335 =
                                           let uu____13341 =
                                             let uu____13343 =
                                               print_implicit q  in
                                             let uu____13345 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____13343 uu____13345
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____13341)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____13335
                                       else ());
                                      (let uu____13351 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____13351, q)))) args wp_args
                           in
                        (head1, uu____13221)  in
                      FStar_Syntax_Syntax.Tm_app uu____13204  in
                    mk1 uu____13203)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____13397 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____13397 with
              | (binders_orig,comp1) ->
                  let uu____13404 =
                    let uu____13421 =
                      FStar_List.map
                        (fun uu____13461  ->
                           match uu____13461 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13489 = is_C h  in
                               if uu____13489
                               then
                                 let w' =
                                   let uu____13505 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13505
                                    in
                                 let uu____13507 =
                                   let uu____13516 =
                                     let uu____13525 =
                                       let uu____13532 =
                                         let uu____13533 =
                                           let uu____13534 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13534  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13533
                                          in
                                       (uu____13532, q)  in
                                     [uu____13525]  in
                                   (w', q) :: uu____13516  in
                                 (w', uu____13507)
                               else
                                 (let x =
                                    let uu____13568 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13568
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____13421  in
                  (match uu____13404 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13642 =
                           let uu____13645 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13645
                            in
                         FStar_Syntax_Subst.subst_comp uu____13642 comp1  in
                       let app =
                         let uu____13649 =
                           let uu____13650 =
                             let uu____13667 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13686 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13687 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13686, uu____13687)) bvs
                                in
                             (wp, uu____13667)  in
                           FStar_Syntax_Syntax.Tm_app uu____13650  in
                         mk1 uu____13649  in
                       let comp3 =
                         let uu____13702 = type_of_comp comp2  in
                         let uu____13703 = is_monadic_comp comp2  in
                         trans_G env uu____13702 uu____13703 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13706,uu____13707) ->
             trans_F_ env e wp
         | uu____13748 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____13756 =
              let uu____13757 = star_type' env h  in
              let uu____13760 =
                let uu____13771 =
                  let uu____13780 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13780)  in
                [uu____13771]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13757;
                FStar_Syntax_Syntax.effect_args = uu____13760;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13756
          else
            (let uu____13806 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13806)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____13827 = n env.tcenv t  in star_type' env uu____13827
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13847 = n env.tcenv t  in check_n env uu____13847
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13864 = n env.tcenv c  in
        let uu____13865 = n env.tcenv wp  in
        trans_F_ env uu____13864 uu____13865
  