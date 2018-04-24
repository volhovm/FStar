open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (no_free_vars :
  (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
    FStar_Pervasives_Native.tuple2)
  =
  let uu____13 = FStar_Syntax_Syntax.new_fv_set () in
  ({
     FStar_Syntax_Syntax.free_names = [];
     FStar_Syntax_Syntax.free_uvars = [];
     FStar_Syntax_Syntax.free_univs = [];
     FStar_Syntax_Syntax.free_univ_names = []
   }, uu____13)
let (singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun fv ->
    let uu____45 =
      let uu____48 = FStar_Syntax_Syntax.new_fv_set () in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v uu____48 in
    ((FStar_Pervasives_Native.fst no_free_vars), uu____45)
let (singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    ((let uu___28_69 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names = [x];
        FStar_Syntax_Syntax.free_uvars =
          (uu___28_69.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___28_69.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___28_69.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_uv :
  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,
     FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    ((let uu___29_120 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___29_120.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars = [x];
        FStar_Syntax_Syntax.free_univs =
          (uu___29_120.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (uu___29_120.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    ((let uu___30_171 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___30_171.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___30_171.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs = [x];
        FStar_Syntax_Syntax.free_univ_names =
          (uu___30_171.FStar_Syntax_Syntax.free_univ_names)
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    ((let uu___31_190 = FStar_Pervasives_Native.fst no_free_vars in
      {
        FStar_Syntax_Syntax.free_names =
          (uu___31_190.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (uu___31_190.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (uu___31_190.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names = [x]
      }), (FStar_Pervasives_Native.snd no_free_vars))
let (union :
  free_vars_and_fvars ->
    free_vars_and_fvars ->
      (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
        FStar_Pervasives_Native.tuple2)
  =
  fun f1 ->
    fun f2 ->
      let uu____211 =
        FStar_Util.set_union (FStar_Pervasives_Native.snd f1)
          (FStar_Pervasives_Native.snd f2) in
      ({
         FStar_Syntax_Syntax.free_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names);
         FStar_Syntax_Syntax.free_uvars =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars);
         FStar_Syntax_Syntax.free_univs =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs);
         FStar_Syntax_Syntax.free_univ_names =
           (FStar_List.append
              (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names
              (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)
       }, uu____211)
let rec (free_univs :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2)
  =
  fun u ->
    let uu____263 = FStar_Syntax_Subst.compress_univ u in
    match uu____263 with
    | FStar_Syntax_Syntax.U_zero -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____270 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out ->
             fun x -> let uu____281 = free_univs x in union out uu____281)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm ->
    fun use_cache ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1 ->
                  fun uu____395 ->
                    match uu____395 with
                    | (x, uu____401) ->
                        let uu____402 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache in
                        union n1 uu____402) no_free_vars) in
        union from_binders from_body in
      let t = FStar_Syntax_Subst.compress tm in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____404 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x, t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____469 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____471 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____472 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
          let f = free_names_and_uvars t1 use_cache in
          FStar_List.fold_left
            (fun out ->
               fun u -> let uu____485 = free_univs u in union out uu____485)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____488) ->
          let uu____509 = free_names_and_uvars t1 use_cache in
          aux_binders bs uu____509
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____528 = free_names_and_uvars_comp c use_cache in
          aux_binders bs uu____528
      | FStar_Syntax_Syntax.Tm_refine (bv, t1) ->
          let uu____535 = free_names_and_uvars t1 use_cache in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____535
      | FStar_Syntax_Syntax.Tm_app (t1, args) ->
          let uu____572 = free_names_and_uvars t1 use_cache in
          free_names_and_uvars_args args uu____572 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
          let uu____617 =
            let uu____638 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1 ->
                 fun uu____661 ->
                   match uu____661 with
                   | (p, wopt, t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache in
                       let n2 = free_names_and_uvars t2 use_cache in
                       let n3 =
                         let uu____711 = FStar_Syntax_Syntax.pat_bvs p in
                         FStar_All.pipe_right uu____711
                           (FStar_List.fold_left
                              (fun n3 ->
                                 fun x ->
                                   let uu____721 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache in
                                   union n3 uu____721) n1) in
                       let uu____722 = union n11 n2 in union n3 uu____722)
              uu____638 in
          FStar_All.pipe_right pats uu____617
      | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____741) ->
          let u1 = free_names_and_uvars t1 use_cache in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____829 = union u1 u2 in
               let uu____830 = free_names_and_uvars tac use_cache in
               union uu____829 uu____830)
      | FStar_Syntax_Syntax.Tm_let (lbs, t1) ->
          let uu____849 =
            let uu____856 = free_names_and_uvars t1 use_cache in
            FStar_List.fold_left
              (fun n1 ->
                 fun lb ->
                   let uu____862 =
                     let uu____863 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache in
                     let uu____864 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache in
                     union uu____863 uu____864 in
                   union n1 uu____862) uu____856 in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____849
      | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_static -> no_free_vars
           | FStar_Syntax_Syntax.Quote_dynamic ->
               free_names_and_uvars tm1 use_cache)
      | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
          let u1 = free_names_and_uvars t1 use_cache in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern args ->
               FStar_List.fold_right
                 (fun a ->
                    fun acc -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____925, t') ->
               let uu____931 = free_names_and_uvars t' use_cache in
               union u1 uu____931
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____932, uu____933, t')
               ->
               let uu____939 = free_names_and_uvars t' use_cache in
               union u1 uu____939
           | FStar_Syntax_Syntax.Meta_labeled uu____940 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____947 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____948 -> u1)
and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t ->
    fun use_cache ->
      let t1 = FStar_Syntax_Subst.compress t in
      let uu____954 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars in
      match uu____954 with
      | FStar_Pervasives_Native.Some n1 when
          let uu____991 = should_invalidate_cache n1 use_cache in
          Prims.op_Negation uu____991 ->
          let uu____992 = FStar_Syntax_Syntax.new_fv_set () in
          (n1, uu____992)
      | uu____997 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
            n1))
and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
    FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.free_vars, FStar_Ident.lident FStar_Util.set)
      FStar_Pervasives_Native.tuple2 -> Prims.bool -> free_vars_and_fvars)
  =
  fun args ->
    fun acc ->
      fun use_cache ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1 ->
                fun uu____1108 ->
                  match uu____1108 with
                  | (x, uu____1116) ->
                      let uu____1121 = free_names_and_uvars x use_cache in
                      union n1 uu____1121) acc)
and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs ->
    fun acc ->
      fun use_cache ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1 ->
                fun uu____1135 ->
                  match uu____1135 with
                  | (x, uu____1141) ->
                      let uu____1142 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache in
                      union n1 uu____1142) acc)
and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c ->
    fun use_cache ->
      let uu____1147 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars in
      match uu____1147 with
      | FStar_Pervasives_Native.Some n1 ->
          let uu____1184 = should_invalidate_cache n1 use_cache in
          if uu____1184
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else
            (let uu____1220 = FStar_Syntax_Syntax.new_fv_set () in
             (n1, uu____1220))
      | uu____1225 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1251 = free_univs u in
                let uu____1252 = free_names_and_uvars t use_cache in
                union uu____1251 uu____1252
            | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u)
                ->
                let uu____1261 = free_univs u in
                let uu____1262 = free_names_and_uvars t use_cache in
                union uu____1261 uu____1262
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1265 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1265 use_cache in
                FStar_List.fold_left
                  (fun us1 ->
                     fun u ->
                       let uu____1277 = free_univs u in union us1 uu____1277)
                  us ct.FStar_Syntax_Syntax.comp_univs in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst n1));
           n1)
and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1 ->
    fun use_cache ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun uu____1345 ->
                  match uu____1345 with
                  | (u, uu____1353) ->
                      let uu____1358 = FStar_Syntax_Unionfind.find u in
                      (match uu____1358 with
                       | FStar_Pervasives_Native.Some uu____1361 -> true
                       | uu____1362 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u ->
                    let uu____1371 = FStar_Syntax_Unionfind.univ_find u in
                    match uu____1371 with
                    | FStar_Pervasives_Native.Some uu____1374 -> true
                    | FStar_Pervasives_Native.None -> false))))
let compare_uv :
  'Auu____1383 'Auu____1384 .
    (FStar_Syntax_Syntax.uvar, 'Auu____1383) FStar_Pervasives_Native.tuple2
      ->
      (FStar_Syntax_Syntax.uvar, 'Auu____1384) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1 ->
    fun uv2 ->
      let uu____1411 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1) in
      let uu____1412 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2) in
      uu____1411 - uu____1412
let (new_uv_set : unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1417 -> FStar_Util.new_set compare_uv
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x ->
    fun y ->
      let uu____1438 = FStar_Syntax_Unionfind.univ_uvar_id x in
      let uu____1439 = FStar_Syntax_Unionfind.univ_uvar_id y in
      uu____1438 - uu____1439
let (new_universe_uvar_set :
  unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1446 -> FStar_Util.new_set compare_universe_uvar
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t ->
    let uu____1458 =
      let uu____1461 =
        let uu____1462 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1462 in
      uu____1461.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1458 FStar_Syntax_Syntax.order_bv
let (uvars :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set)
  =
  fun t ->
    let uu____1482 =
      let uu____1501 =
        let uu____1502 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1502 in
      uu____1501.FStar_Syntax_Syntax.free_uvars in
    FStar_Util.as_set uu____1482 compare_uv
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t ->
    let uu____1538 =
      let uu____1541 =
        let uu____1542 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1542 in
      uu____1541.FStar_Syntax_Syntax.free_univs in
    FStar_Util.as_set uu____1538 compare_universe_uvar
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t ->
    let uu____1558 =
      let uu____1561 =
        let uu____1562 = free_names_and_uvars t true in
        FStar_Pervasives_Native.fst uu____1562 in
      uu____1561.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1558 FStar_Syntax_Syntax.order_univ_name
let (univnames_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun c ->
    let uu____1578 =
      let uu____1581 =
        let uu____1582 = free_names_and_uvars_comp c true in
        FStar_Pervasives_Native.fst uu____1582 in
      uu____1581.FStar_Syntax_Syntax.free_univ_names in
    FStar_Util.as_set uu____1578 FStar_Syntax_Syntax.order_univ_name
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t ->
    let uu____1598 = free_names_and_uvars t false in
    FStar_Pervasives_Native.snd uu____1598
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs ->
    let uu____1614 =
      let uu____1617 =
        let uu____1618 = free_names_and_uvars_binders bs no_free_vars true in
        FStar_Pervasives_Native.fst uu____1618 in
      uu____1617.FStar_Syntax_Syntax.free_names in
    FStar_Util.as_set uu____1614 FStar_Syntax_Syntax.order_bv