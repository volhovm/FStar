open Prims
let subst_to_string :
  'Auu____4 . (FStar_Syntax_Syntax.bv * 'Auu____4) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____44  ->
              match uu____44 with
              | (b,uu____51) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____66 'Auu____67 .
    ('Auu____66 -> 'Auu____67 FStar_Pervasives_Native.option) ->
      'Auu____66 Prims.list ->
        ('Auu____66 Prims.list * 'Auu____67) FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____109 = f s0  in
          (match uu____109 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____142 'Auu____143 'Auu____144 .
    ('Auu____142 -> 'Auu____143 -> 'Auu____144) ->
      'Auu____144 ->
        ('Auu____142 * 'Auu____143) FStar_Pervasives_Native.option ->
          'Auu____144
  =
  fun f  ->
    fun x  ->
      fun uu___0_171  ->
        match uu___0_171 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____207 'Auu____208 'Auu____209 .
    ('Auu____207 -> 'Auu____208 FStar_Pervasives_Native.option) ->
      'Auu____207 Prims.list ->
        ('Auu____207 Prims.list -> 'Auu____208 -> 'Auu____209) ->
          'Auu____209 -> 'Auu____209
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____257 = apply_until_some f s  in
          FStar_All.pipe_right uu____257 (map_some_curry g t)
  
let compose_subst :
  'Auu____283 .
    ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____283 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____334 ->
            FStar_Pervasives_Native.snd s2
        | uu____337 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____420 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____446;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____447;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____448;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____449;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____450;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____451;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____452;_},s)
        ->
        let uu____501 = FStar_Syntax_Unionfind.find uv  in
        (match uu____501 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____512 =
               let uu____515 =
                 let uu____523 = delay t' s  in force_uvar' uu____523  in
               FStar_Pervasives_Native.fst uu____515  in
             (uu____512, true)
         | uu____533 -> (t, false))
    | uu____540 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____562 = force_uvar' t  in
    match uu____562 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____598 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____598, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____672 = FStar_ST.op_Bang m  in
        (match uu____672 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____722 = try_read_memo_aux t'  in
             (match uu____722 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____782 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____799 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____799
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____825 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____825 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____829 -> u)
    | uu____832 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___1_854  ->
           match uu___1_854 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____862 =
                 let uu____863 =
                   let uu____864 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____864  in
                 FStar_Syntax_Syntax.bv_to_name uu____863  in
               FStar_Pervasives_Native.Some uu____862
           | uu____865 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___2_891  ->
           match uu___2_891 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____900 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___108_905 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___108_905.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___108_905.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____900
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____916 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___3_941  ->
           match uu___3_941 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____949 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___4_970  ->
           match uu___4_970 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____978 -> FStar_Pervasives_Native.None)
  
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u  in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____1006 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____1016 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____1016
      | FStar_Syntax_Syntax.U_max us ->
          let uu____1020 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____1020
  
let tag_with_range :
  'Auu____1030 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____1030 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1056 =
            let uu____1058 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1059 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1058 uu____1059  in
          if uu____1056
          then t
          else
            (let r1 =
               let uu____1066 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1066
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1069 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1069
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1071 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1071
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___160_1077 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1078 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1078;
                       FStar_Syntax_Syntax.p =
                         (uu___160_1077.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___163_1080 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___163_1080.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___163_1080.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___168_1082 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___168_1082.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1092 .
    FStar_Ident.lident ->
      ('Auu____1092 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1112 =
            let uu____1114 =
              let uu____1115 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1115  in
            let uu____1116 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1114 uu____1116  in
          if uu____1112
          then l
          else
            (let uu____1120 =
               let uu____1121 = FStar_Ident.range_of_lid l  in
               let uu____1122 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1121 uu____1122  in
             FStar_Ident.set_lid_range l uu____1120)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1139 =
            let uu____1141 = FStar_Range.use_range r  in
            let uu____1142 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1141 uu____1142  in
          if uu____1139
          then r
          else
            (let uu____1146 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1146)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1267 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1275 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1280 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1349 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1350 =
                 let uu____1357 =
                   let uu____1358 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1358  in
                 FStar_Syntax_Syntax.mk uu____1357  in
               uu____1350 FStar_Pervasives_Native.None uu____1349
           | uu____1363 ->
               let uu____1364 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1364)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___5_1376  ->
              match uu___5_1376 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1380 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1380
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1408 ->
          let uu___229_1417 = t  in
          let uu____1418 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1423 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1428 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1431 =
            FStar_List.map
              (fun uu____1459  ->
                 match uu____1459 with
                 | (t1,imp) ->
                     let uu____1478 = subst' s t1  in
                     let uu____1479 = subst_imp' s imp  in
                     (uu____1478, uu____1479))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1484 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1418;
            FStar_Syntax_Syntax.effect_name = uu____1423;
            FStar_Syntax_Syntax.result_typ = uu____1428;
            FStar_Syntax_Syntax.effect_args = uu____1431;
            FStar_Syntax_Syntax.flags = uu____1484
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1515 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1536 = subst' s t1  in
               let uu____1537 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1536 uu____1537
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1554 = subst' s t1  in
               let uu____1555 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1554 uu____1555
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1563 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1563)

and (subst_imp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____1581 =
            let uu____1582 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____1582  in
          FStar_Pervasives_Native.Some uu____1581
      | i1 -> i1

let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1621 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1648 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____1648)
  =
  fun n1  ->
    fun s  ->
      let uu____1679 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1679, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____1722  ->
      match uu____1722 with
      | (x,imp) ->
          let uu____1749 =
            let uu___288_1750 = x  in
            let uu____1751 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___288_1750.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___288_1750.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1751
            }  in
          let uu____1754 = subst_imp' s imp  in (uu____1749, uu____1754)
  
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1860 = shift_subst' i s  in
                   subst_binder' uu____1860 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1899 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1899) ->
        (FStar_Syntax_Syntax.term * 'Auu____1899)
  =
  fun s  ->
    fun uu____1917  ->
      match uu____1917 with
      | (t,imp) -> let uu____1924 = subst' s t  in (uu____1924, imp)
  
let subst_args' :
  'Auu____1931 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____1931) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1931) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____2025 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____2047 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____2109  ->
                      fun uu____2110  ->
                        match (uu____2109, uu____2110) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____2206 = aux n2 p2  in
                            (match uu____2206 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____2047 with
             | (pats1,n2) ->
                 ((let uu___325_2280 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___325_2280.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___330_2306 = x  in
              let uu____2307 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___330_2306.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___330_2306.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2307
              }  in
            ((let uu___333_2312 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___333_2312.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___338_2325 = x  in
              let uu____2326 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___338_2325.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___338_2325.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2326
              }  in
            ((let uu___341_2331 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___341_2331.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___348_2349 = x  in
              let uu____2350 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___348_2349.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___348_2349.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2350
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___352_2356 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___352_2356.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2382 =
            let uu___359_2383 = rc  in
            let uu____2384 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___359_2383.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2384;
              FStar_Syntax_Syntax.residual_flags =
                (uu___359_2383.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2382
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____2434  ->
                  match uu____2434 with
                  | (x',uu____2443) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___7_2459 =
          match uu___7_2459 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___6_2490  ->
                        match uu___6_2490 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2499 = should_retain x  in
                            if uu____2499
                            then
                              let uu____2504 =
                                let uu____2505 =
                                  let uu____2512 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2512)  in
                                FStar_Syntax_Syntax.NT uu____2505  in
                              [uu____2504]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2527 = should_retain x  in
                            if uu____2527
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___386_2535 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___386_2535.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___386_2535.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____2545 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2550 -> []))
                 in
              let uu____2551 = aux rest  in FStar_List.append hd1 uu____2551
           in
        let uu____2554 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2554 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2617 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2617  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2620 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____2649 ->
               let t1 =
                 let uu____2659 =
                   let uu____2668 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2668  in
                 uu____2659 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____2718 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____2719 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2724 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2751 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2751 with
           | FStar_Pervasives_Native.None  ->
               let uu____2756 =
                 let uu___419_2759 = t  in
                 let uu____2762 =
                   let uu____2763 =
                     let uu____2776 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2776)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2763  in
                 {
                   FStar_Syntax_Syntax.n = uu____2762;
                   FStar_Syntax_Syntax.pos =
                     (uu___419_2759.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___419_2759.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2756 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2800 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2801 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2802 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2816 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2816 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2849 =
            let uu____2850 =
              let uu____2867 = subst' s t0  in
              let uu____2870 = subst_args' s args  in
              (uu____2867, uu____2870)  in
            FStar_Syntax_Syntax.Tm_app uu____2850  in
          mk1 uu____2849
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2971 = subst' s t1  in FStar_Util.Inl uu____2971
            | FStar_Util.Inr c ->
                let uu____2985 = subst_comp' s c  in
                FStar_Util.Inr uu____2985
             in
          let uu____2992 =
            let uu____2993 =
              let uu____3020 = subst' s t0  in
              let uu____3023 =
                let uu____3040 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____3040)  in
              (uu____3020, uu____3023, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2993  in
          mk1 uu____2992
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____3122 =
            let uu____3123 =
              let uu____3142 = subst_binders' s bs  in
              let uu____3151 = subst' s' body  in
              let uu____3154 = push_subst_lcomp s' lopt  in
              (uu____3142, uu____3151, uu____3154)  in
            FStar_Syntax_Syntax.Tm_abs uu____3123  in
          mk1 uu____3122
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____3198 =
            let uu____3199 =
              let uu____3214 = subst_binders' s bs  in
              let uu____3223 =
                let uu____3226 = shift_subst' n1 s  in
                subst_comp' uu____3226 comp  in
              (uu____3214, uu____3223)  in
            FStar_Syntax_Syntax.Tm_arrow uu____3199  in
          mk1 uu____3198
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___466_3252 = x  in
            let uu____3253 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___466_3252.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___466_3252.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3253
            }  in
          let phi1 =
            let uu____3257 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____3257 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____3373  ->
                    match uu____3373 with
                    | (pat,wopt,branch) ->
                        let uu____3403 = subst_pat' s pat  in
                        (match uu____3403 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3434 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3434
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs  in
          let sn = shift_subst' n1 s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3502 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3502
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___504_3520 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_3520.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_3520.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___509_3522 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___509_3522.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___509_3522.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___509_3522.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___509_3522.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3553 =
            let uu____3554 =
              let uu____3561 = subst' s t0  in
              let uu____3564 =
                let uu____3565 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3565  in
              (uu____3561, uu____3564)  in
            FStar_Syntax_Syntax.Tm_meta uu____3554  in
          mk1 uu____3553
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3631 =
            let uu____3632 =
              let uu____3639 = subst' s t0  in
              let uu____3642 =
                let uu____3643 =
                  let uu____3650 = subst' s t1  in (m, uu____3650)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3643  in
              (uu____3639, uu____3642)  in
            FStar_Syntax_Syntax.Tm_meta uu____3632  in
          mk1 uu____3631
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3669 =
            let uu____3670 =
              let uu____3677 = subst' s t0  in
              let uu____3680 =
                let uu____3681 =
                  let uu____3690 = subst' s t1  in (m1, m2, uu____3690)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3681  in
              (uu____3677, uu____3680)  in
            FStar_Syntax_Syntax.Tm_meta uu____3670  in
          mk1 uu____3669
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3705 =
                 let uu____3706 =
                   let uu____3713 = subst' s tm  in (uu____3713, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3706  in
               mk1 uu____3705
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3727 =
            let uu____3728 = let uu____3735 = subst' s t1  in (uu____3735, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3728  in
          mk1 uu____3727
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3749 = force_uvar t1  in
    match uu____3749 with
    | (t2,uu____3758) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3811 =
                 let uu____3816 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3816  in
               FStar_ST.op_Colon_Equals memo uu____3811);
              compress t2)
         | uu____3848 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3883 =
        let uu____3884 =
          let uu____3885 =
            let uu____3886 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3886  in
          FStar_Syntax_Syntax.SomeUseRange uu____3885  in
        ([], uu____3884)  in
      subst' uu____3883 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  =
  fun s  -> fun imp  -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3947 =
      FStar_List.fold_right
        (fun uu____3974  ->
           fun uu____3975  ->
             match (uu____3974, uu____3975) with
             | ((x,uu____4010),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3947 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___581_4168 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4169 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___581_4168.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___581_4168.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4169
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____4176 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4176
             in
          let uu____4182 = aux bs' o1  in
          (match uu____4182 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____4243 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____4243
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____4281 = open_binders' bs  in
      match uu____4281 with
      | (bs',opening) ->
          let uu____4318 = subst opening t  in (bs', uu____4318, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____4334 = open_term' bs t  in
      match uu____4334 with | (b,t1,uu____4347) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____4363 = open_binders' bs  in
      match uu____4363 with
      | (bs',opening) ->
          let uu____4398 = subst_comp opening t  in (bs', uu____4398)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4448 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4473 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4544  ->
                    fun uu____4545  ->
                      match (uu____4544, uu____4545) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4659 = open_pat_aux sub2 p2  in
                          (match uu____4659 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4473 with
           | (pats1,sub2) ->
               ((let uu___628_4769 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___628_4769.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___632_4790 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4791 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___632_4790.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___632_4790.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4791
            }  in
          let sub2 =
            let uu____4797 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4797
             in
          ((let uu___636_4808 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___636_4808.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___640_4813 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4814 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___640_4813.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___640_4813.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4814
            }  in
          let sub2 =
            let uu____4820 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4820
             in
          ((let uu___644_4831 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___644_4831.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___650_4841 = x  in
            let uu____4842 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___650_4841.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___650_4841.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4842
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___654_4851 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___654_4851.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____4865  ->
    match uu____4865 with
    | (p,wopt,e) ->
        let uu____4889 = open_pat p  in
        (match uu____4889 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4918 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4918
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4938 = open_branch' br  in
    match uu____4938 with | (br1,uu____4944) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4956 = closing_subst bs  in subst uu____4956 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4970 = closing_subst bs  in subst_comp uu____4970 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___686_5038 = x  in
            let uu____5039 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___686_5038.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___686_5038.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5039
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____5046 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5046
             in
          let uu____5052 = aux s' tl1  in (x1, imp1) :: uu____5052
       in
    aux [] bs
  
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____5079  ->
           let uu____5080 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____5080)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____5134 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____5159 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____5230  ->
                    fun uu____5231  ->
                      match (uu____5230, uu____5231) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____5345 = aux sub2 p2  in
                          (match uu____5345 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____5159 with
           | (pats1,sub2) ->
               ((let uu___717_5455 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___717_5455.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___721_5476 = x  in
            let uu____5477 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___721_5476.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___721_5476.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5477
            }  in
          let sub2 =
            let uu____5483 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5483
             in
          ((let uu___725_5494 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___725_5494.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___729_5499 = x  in
            let uu____5500 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___729_5499.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___729_5499.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5500
            }  in
          let sub2 =
            let uu____5506 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____5506
             in
          ((let uu___733_5517 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___733_5517.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___739_5527 = x  in
            let uu____5528 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___739_5527.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___739_5527.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____5528
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___743_5537 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___743_5537.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____5547  ->
    match uu____5547 with
    | (p,wopt,e) ->
        let uu____5567 = close_pat p  in
        (match uu____5567 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5604 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5604
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____5692 = univ_var_opening us  in
      match uu____5692 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____5735 = univ_var_opening us  in
      match uu____5735 with
      | (s,us') -> let uu____5758 = subst_comp s c  in (us', uu____5758)
  
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____5821 =
        let uu____5833 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5833
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5873  ->
                 match uu____5873 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5910 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5910  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___795_5918 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___795_5918.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___795_5918.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___795_5918.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___795_5918.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___795_5918.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___795_5918.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5821 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5961 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5991  ->
                             match uu____5991 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5961 with
                    | (uu____6040,us,u_let_rec_opening) ->
                        let uu___812_6053 = lb  in
                        let uu____6054 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6057 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___812_6053.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____6054;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___812_6053.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6057;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___812_6053.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___812_6053.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____6084 =
        let uu____6092 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____6092
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____6121  ->
                 match uu____6121 with
                 | (i,out) ->
                     let uu____6144 =
                       let uu____6147 =
                         let uu____6148 =
                           let uu____6154 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____6154, i)  in
                         FStar_Syntax_Syntax.NM uu____6148  in
                       uu____6147 :: out  in
                     ((i + (Prims.parse_int "1")), uu____6144)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____6084 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____6193 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____6213  ->
                             match uu____6213 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____6193 with
                    | (uu____6244,u_let_rec_closing) ->
                        let uu___834_6252 = lb  in
                        let uu____6253 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____6256 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___834_6252.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___834_6252.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____6253;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___834_6252.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____6256;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___834_6252.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___834_6252.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____6272  ->
      match uu____6272 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____6307  ->
                   match uu____6307 with
                   | (x,uu____6316) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____6337  ->
      match uu____6337 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____6361 = subst s t  in (us', uu____6361)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____6380  ->
      match uu____6380 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____6394 = subst s1 t  in (us, uu____6394)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____6435  ->
              match uu____6435 with
              | (x,uu____6444) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun b  ->
    fun t  ->
      let uu____6471 = open_term [b] t  in
      match uu____6471 with
      | (b1::[],t1) -> (b1, t1)
      | uu____6512 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____6543 =
        let uu____6548 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____6548 t  in
      match uu____6543 with
      | (bs,t1) ->
          let uu____6563 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____6563, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____6591 = open_term_bvs [bv] t  in
      match uu____6591 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____6606 -> failwith "impossible: open_term_bv"
  