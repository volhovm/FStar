open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____104  ->
                match uu____104 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____159  ->
                             match uu____159 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____177 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____177 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____183 =
                                     let uu____184 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____184]  in
                                   FStar_Syntax_Subst.close uu____183 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___248_241  ->
        match uu___248_241 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___249_261  ->
    match uu___249_261 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___250_279  ->
    match uu___250_279 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____282 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____290 .
    FStar_Parser_AST.imp ->
      'Auu____290 ->
        ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____316 .
    FStar_Parser_AST.imp ->
      'Auu____316 ->
        ('Auu____316 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____335 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____356 -> true
            | uu____362 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____371 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____378 =
      let uu____379 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____379  in
    FStar_Parser_AST.mk_term uu____378 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____389 =
      let uu____390 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____390  in
    FStar_Parser_AST.mk_term uu____389 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____406 =
        let uu____407 = unparen t  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.Name l ->
          let uu____410 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____410 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____417) ->
          let uu____430 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____430 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____437,uu____438) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____443,uu____444) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____449,t1) -> is_comp_type env t1
      | uu____451 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____474 =
          let uu____477 =
            let uu____478 =
              let uu____484 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____484, r)  in
            FStar_Ident.mk_ident uu____478  in
          [uu____477]  in
        FStar_All.pipe_right uu____474 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____500 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____500 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____538 =
              let uu____539 =
                let uu____540 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____540 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____539 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____538  in
          let fallback uu____548 =
            let uu____549 = FStar_Ident.text_of_id op  in
            match uu____549 with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.delta_equational
            | "@" ->
                let uu____570 = FStar_Options.ml_ish ()  in
                if uu____570
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.delta_equational
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | uu____596 -> FStar_Pervasives_Native.None  in
          let uu____598 =
            let uu____601 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____601  in
          match uu____598 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____605 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____620 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____620
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____669 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____673 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____673 with | (env1,uu____685) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____688,term) ->
          let uu____690 = free_type_vars env term  in (env, uu____690)
      | FStar_Parser_AST.TAnnotated (id1,uu____696) ->
          let uu____697 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____697 with | (env1,uu____709) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____713 = free_type_vars env t  in (env, uu____713)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____720 =
        let uu____721 = unparen t  in uu____721.FStar_Parser_AST.tm  in
      match uu____720 with
      | FStar_Parser_AST.Labeled uu____724 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____737 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____737 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____742 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____745 -> []
      | FStar_Parser_AST.Uvar uu____746 -> []
      | FStar_Parser_AST.Var uu____747 -> []
      | FStar_Parser_AST.Projector uu____748 -> []
      | FStar_Parser_AST.Discrim uu____753 -> []
      | FStar_Parser_AST.Name uu____754 -> []
      | FStar_Parser_AST.Requires (t1,uu____756) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____764) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____771,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____790,ts) ->
          FStar_List.collect
            (fun uu____811  ->
               match uu____811 with | (t1,uu____819) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____820,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____828) ->
          let uu____829 = free_type_vars env t1  in
          let uu____832 = free_type_vars env t2  in
          FStar_List.append uu____829 uu____832
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____837 = free_type_vars_b env b  in
          (match uu____837 with
           | (env1,f) ->
               let uu____852 = free_type_vars env1 t1  in
               FStar_List.append f uu____852)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____869 =
            FStar_List.fold_left
              (fun uu____893  ->
                 fun bt  ->
                   match uu____893 with
                   | (env1,free) ->
                       let uu____917 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____932 = free_type_vars env1 body  in
                             (env1, uu____932)
                          in
                       (match uu____917 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____869 with
           | (env1,free) ->
               let uu____961 = free_type_vars env1 body  in
               FStar_List.append free uu____961)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____970 =
            FStar_List.fold_left
              (fun uu____990  ->
                 fun binder  ->
                   match uu____990 with
                   | (env1,free) ->
                       let uu____1010 = free_type_vars_b env1 binder  in
                       (match uu____1010 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____970 with
           | (env1,free) ->
               let uu____1041 = free_type_vars env1 body  in
               FStar_List.append free uu____1041)
      | FStar_Parser_AST.Project (t1,uu____1045) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1056 = free_type_vars env rel  in
          let uu____1059 =
            let uu____1062 = free_type_vars env init1  in
            let uu____1065 =
              FStar_List.collect
                (fun uu____1074  ->
                   match uu____1074 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1080 = free_type_vars env rel1  in
                       let uu____1083 =
                         let uu____1086 = free_type_vars env just  in
                         let uu____1089 = free_type_vars env next  in
                         FStar_List.append uu____1086 uu____1089  in
                       FStar_List.append uu____1080 uu____1083) steps
               in
            FStar_List.append uu____1062 uu____1065  in
          FStar_List.append uu____1056 uu____1059
      | FStar_Parser_AST.Abs uu____1092 -> []
      | FStar_Parser_AST.Let uu____1099 -> []
      | FStar_Parser_AST.LetOpen uu____1120 -> []
      | FStar_Parser_AST.If uu____1125 -> []
      | FStar_Parser_AST.QForall uu____1132 -> []
      | FStar_Parser_AST.QExists uu____1145 -> []
      | FStar_Parser_AST.Record uu____1158 -> []
      | FStar_Parser_AST.Match uu____1171 -> []
      | FStar_Parser_AST.TryWith uu____1186 -> []
      | FStar_Parser_AST.Bind uu____1201 -> []
      | FStar_Parser_AST.Quote uu____1208 -> []
      | FStar_Parser_AST.VQuote uu____1213 -> []
      | FStar_Parser_AST.Antiquote uu____1214 -> []
      | FStar_Parser_AST.Seq uu____1215 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1269 =
        let uu____1270 = unparen t1  in uu____1270.FStar_Parser_AST.tm  in
      match uu____1269 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1312 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1337 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1337  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1359 =
                     let uu____1360 =
                       let uu____1365 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1365)  in
                     FStar_Parser_AST.TAnnotated uu____1360  in
                   FStar_Parser_AST.mk_binder uu____1359
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1383 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1383  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1405 =
                     let uu____1406 =
                       let uu____1411 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1411)  in
                     FStar_Parser_AST.TAnnotated uu____1406  in
                   FStar_Parser_AST.mk_binder uu____1405
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1413 =
             let uu____1414 = unparen t  in uu____1414.FStar_Parser_AST.tm
              in
           match uu____1413 with
           | FStar_Parser_AST.Product uu____1415 -> t
           | uu____1422 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1459 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1470 -> true
    | FStar_Parser_AST.PatTvar (uu____1474,uu____1475) -> true
    | FStar_Parser_AST.PatVar (uu____1481,uu____1482) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1489) -> is_var_pattern p1
    | uu____1502 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1513) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1526;
           FStar_Parser_AST.prange = uu____1527;_},uu____1528)
        -> true
    | uu____1540 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1556 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1629 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1629 with
             | (name,args,uu____1672) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1722);
               FStar_Parser_AST.prange = uu____1723;_},args)
            when is_top_level1 ->
            let uu____1733 =
              let uu____1738 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1738  in
            (uu____1733, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1760);
               FStar_Parser_AST.prange = uu____1761;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1791 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun acc  ->
      fun p  ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc
           in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____1850 -> acc
        | FStar_Parser_AST.PatName uu____1853 -> acc
        | FStar_Parser_AST.PatOp uu____1854 -> acc
        | FStar_Parser_AST.PatConst uu____1855 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1872) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1878) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1887) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1904 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1904
        | FStar_Parser_AST.PatAscribed (pat,uu____1912) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
  
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun p  ->
      let acc =
        FStar_Util.new_set
          (fun id1  ->
             fun id2  ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then (Prims.parse_int "0")
               else (Prims.parse_int "1"))
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1994 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2036 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___251_2085  ->
    match uu___251_2085 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2092 -> failwith "Impossible"
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2127  ->
    match uu____2127 with
    | (attrs,n1,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs;
          FStar_Syntax_Syntax.lbpos = pos
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2209 =
        let uu____2226 =
          let uu____2229 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2229  in
        let uu____2230 =
          let uu____2241 =
            let uu____2250 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2250)  in
          [uu____2241]  in
        (uu____2226, uu____2230)  in
      FStar_Syntax_Syntax.Tm_app uu____2209  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2299 =
        let uu____2316 =
          let uu____2319 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2319  in
        let uu____2320 =
          let uu____2331 =
            let uu____2340 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2340)  in
          [uu____2331]  in
        (uu____2316, uu____2320)  in
      FStar_Syntax_Syntax.Tm_app uu____2299  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____2403 =
            let uu____2420 =
              let uu____2423 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2423  in
            let uu____2424 =
              let uu____2435 =
                let uu____2444 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2444)  in
              let uu____2452 =
                let uu____2463 =
                  let uu____2472 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2472)  in
                [uu____2463]  in
              uu____2435 :: uu____2452  in
            (uu____2420, uu____2424)  in
          FStar_Syntax_Syntax.Tm_app uu____2403  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2532 =
        let uu____2547 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2566  ->
               match uu____2566 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2577;
                    FStar_Syntax_Syntax.index = uu____2578;
                    FStar_Syntax_Syntax.sort = t;_},uu____2580)
                   ->
                   let uu____2588 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2588) uu____2547
         in
      FStar_All.pipe_right bs uu____2532  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2604 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2622 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2650 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2671,uu____2672,bs,t,uu____2675,uu____2676)
                            ->
                            let uu____2685 = bs_univnames bs  in
                            let uu____2688 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2685 uu____2688
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2691,uu____2692,t,uu____2694,uu____2695,uu____2696)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2703 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2650 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___280_2712 = s  in
        let uu____2713 =
          let uu____2714 =
            let uu____2723 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2741,bs,t,lids1,lids2) ->
                          let uu___281_2754 = se  in
                          let uu____2755 =
                            let uu____2756 =
                              let uu____2773 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2774 =
                                let uu____2775 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2775 t  in
                              (lid, uvs, uu____2773, uu____2774, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2756
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2755;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___281_2754.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___281_2754.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___281_2754.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___281_2754.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2789,t,tlid,n1,lids1) ->
                          let uu___282_2800 = se  in
                          let uu____2801 =
                            let uu____2802 =
                              let uu____2818 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2818, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2802  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2801;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___282_2800.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___282_2800.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___282_2800.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___282_2800.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2822 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2723, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2714  in
        {
          FStar_Syntax_Syntax.sigel = uu____2713;
          FStar_Syntax_Syntax.sigrng =
            (uu___280_2712.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___280_2712.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___280_2712.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___280_2712.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2829,t) ->
        let uvs =
          let uu____2832 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2832 FStar_Util.set_elements  in
        let uu___283_2837 = s  in
        let uu____2838 =
          let uu____2839 =
            let uu____2846 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2846)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2839  in
        {
          FStar_Syntax_Syntax.sigel = uu____2838;
          FStar_Syntax_Syntax.sigrng =
            (uu___283_2837.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___283_2837.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___283_2837.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___283_2837.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2870 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2873 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2880) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2913,(FStar_Util.Inl t,uu____2915),uu____2916)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2963,(FStar_Util.Inr c,uu____2965),uu____2966)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3013 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3014,(FStar_Util.Inl t,uu____3016),uu____3017) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3064,(FStar_Util.Inr c,uu____3066),uu____3067) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3114 -> empty_set  in
          FStar_Util.set_union uu____2870 uu____2873  in
        let all_lb_univs =
          let uu____3118 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3134 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3134) empty_set)
             in
          FStar_All.pipe_right uu____3118 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___284_3144 = s  in
        let uu____3145 =
          let uu____3146 =
            let uu____3153 =
              let uu____3154 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___285_3166 = lb  in
                        let uu____3167 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3170 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___285_3166.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3167;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___285_3166.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3170;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___285_3166.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___285_3166.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3154)  in
            (uu____3153, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3146  in
        {
          FStar_Syntax_Syntax.sigel = uu____3145;
          FStar_Syntax_Syntax.sigrng =
            (uu___284_3144.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___284_3144.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___284_3144.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___284_3144.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3179,fml) ->
        let uvs =
          let uu____3182 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3182 FStar_Util.set_elements  in
        let uu___286_3187 = s  in
        let uu____3188 =
          let uu____3189 =
            let uu____3196 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3196)  in
          FStar_Syntax_Syntax.Sig_assume uu____3189  in
        {
          FStar_Syntax_Syntax.sigel = uu____3188;
          FStar_Syntax_Syntax.sigrng =
            (uu___286_3187.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___286_3187.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___286_3187.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___286_3187.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3198,bs,c,flags1) ->
        let uvs =
          let uu____3207 =
            let uu____3210 = bs_univnames bs  in
            let uu____3213 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3210 uu____3213  in
          FStar_All.pipe_right uu____3207 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___287_3221 = s  in
        let uu____3222 =
          let uu____3223 =
            let uu____3236 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3237 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3236, uu____3237, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3223  in
        {
          FStar_Syntax_Syntax.sigel = uu____3222;
          FStar_Syntax_Syntax.sigrng =
            (uu___287_3221.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___287_3221.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___287_3221.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___287_3221.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3240 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___252_3248  ->
    match uu___252_3248 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "null_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "interp" -> true
    | "mrelation" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3303 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3324 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3324)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3350 =
      let uu____3351 = unparen t  in uu____3351.FStar_Parser_AST.tm  in
    match uu____3350 with
    | FStar_Parser_AST.Wild  ->
        let uu____3357 =
          let uu____3358 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3358  in
        FStar_Util.Inr uu____3357
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3371)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.strcat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____3462 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3462
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3479 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3479
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3495 =
               let uu____3501 =
                 let uu____3503 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3503
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3501)
                in
             FStar_Errors.raise_error uu____3495 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3512 ->
        let rec aux t1 univargs =
          let uu____3549 =
            let uu____3550 = unparen t1  in uu____3550.FStar_Parser_AST.tm
             in
          match uu____3549 with
          | FStar_Parser_AST.App (t2,targ,uu____3558) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___253_3585  ->
                     match uu___253_3585 with
                     | FStar_Util.Inr uu____3592 -> true
                     | uu____3595 -> false) univargs
              then
                let uu____3603 =
                  let uu____3604 =
                    FStar_List.map
                      (fun uu___254_3614  ->
                         match uu___254_3614 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3604  in
                FStar_Util.Inr uu____3603
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___255_3640  ->
                        match uu___255_3640 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3650 -> failwith "impossible")
                     univargs
                    in
                 let uu____3654 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3654)
          | uu____3670 ->
              let uu____3671 =
                let uu____3677 =
                  let uu____3679 =
                    let uu____3681 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3681 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3679  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3677)  in
              FStar_Errors.raise_error uu____3671 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3696 ->
        let uu____3697 =
          let uu____3703 =
            let uu____3705 =
              let uu____3707 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3707 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3705  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3703)  in
        FStar_Errors.raise_error uu____3697 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____3748;_});
            FStar_Syntax_Syntax.pos = uu____3749;
            FStar_Syntax_Syntax.vars = uu____3750;_})::uu____3751
        ->
        let uu____3782 =
          let uu____3788 =
            let uu____3790 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3790
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3788)  in
        FStar_Errors.raise_error uu____3782 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3796 ->
        let uu____3815 =
          let uu____3821 =
            let uu____3823 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3823
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3821)  in
        FStar_Errors.raise_error uu____3815 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3836 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____3836) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3864 = FStar_List.hd fields  in
        match uu____3864 with
        | (f,uu____3874) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3886 =
                match uu____3886 with
                | (f',uu____3892) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3894 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3894
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____3904 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3904);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____4296 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4303 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4304 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4306,pats1) ->
              let aux out uu____4347 =
                match uu____4347 with
                | (p2,uu____4360) ->
                    let intersection =
                      let uu____4370 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4370 out  in
                    let uu____4373 = FStar_Util.set_is_empty intersection  in
                    if uu____4373
                    then
                      let uu____4378 = pat_vars p2  in
                      FStar_Util.set_union out uu____4378
                    else
                      (let duplicate_bv =
                         let uu____4384 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4384  in
                       let uu____4387 =
                         let uu____4393 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4393)
                          in
                       FStar_Errors.raise_error uu____4387 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4417 = pat_vars p1  in
            FStar_All.pipe_right uu____4417 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4445 =
                let uu____4447 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4447  in
              if uu____4445
              then ()
              else
                (let nonlinear_vars =
                   let uu____4456 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4456  in
                 let first_nonlinear_var =
                   let uu____4460 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4460  in
                 let uu____4463 =
                   let uu____4469 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4469)  in
                 FStar_Errors.raise_error uu____4463 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4497 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4497 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4514 ->
            let uu____4517 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4517 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4668 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4692 =
              let uu____4693 =
                let uu____4694 =
                  let uu____4701 =
                    let uu____4702 =
                      let uu____4708 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4708, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4702  in
                  (uu____4701, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4694  in
              {
                FStar_Parser_AST.pat = uu____4693;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4692
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4728 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4731 = aux loc env1 p2  in
              match uu____4731 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___288_4820 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___289_4825 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___289_4825.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___289_4825.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___288_4820.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___290_4827 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___291_4832 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___291_4832.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___291_4832.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___290_4827.FStar_Syntax_Syntax.p)
                        }
                    | uu____4833 when top -> p4
                    | uu____4834 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4839 =
                    match binder with
                    | LetBinder uu____4860 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4885 = close_fun env1 t  in
                          desugar_term env1 uu____4885  in
                        let x1 =
                          let uu___292_4887 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___292_4887.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___292_4887.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4839 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4955 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4955, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4969 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4969, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4993 = resolvex loc env1 x  in
            (match uu____4993 with
             | (loc1,env2,xbv) ->
                 let uu____5022 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5022, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5045 = resolvex loc env1 x  in
            (match uu____5045 with
             | (loc1,env2,xbv) ->
                 let uu____5074 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5074, [], imp))
        | FStar_Parser_AST.PatName l ->
            let l1 =
              FStar_Syntax_DsEnv.fail_or env1
                (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
               in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5089 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5089, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5119;_},args)
            ->
            let uu____5125 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5186  ->
                     match uu____5186 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5267 = aux loc1 env2 arg  in
                         (match uu____5267 with
                          | (loc2,env3,uu____5314,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5125 with
             | (loc1,env2,annots,args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____5446 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5446, annots, false))
        | FStar_Parser_AST.PatApp uu____5464 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5495 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5546  ->
                     match uu____5546 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5607 = aux loc1 env2 pat  in
                         (match uu____5607 with
                          | (loc2,env3,uu____5649,pat1,ans,uu____5652) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5495 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5749 =
                     let uu____5752 =
                       let uu____5759 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5759  in
                     let uu____5760 =
                       let uu____5761 =
                         let uu____5775 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5775, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5761  in
                     FStar_All.pipe_left uu____5752 uu____5760  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5809 =
                            let uu____5810 =
                              let uu____5824 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5824, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5810  in
                          FStar_All.pipe_left (pos_r r) uu____5809) pats1
                     uu____5749
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____5882 =
              FStar_List.fold_left
                (fun uu____5942  ->
                   fun p2  ->
                     match uu____5942 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6024 = aux loc1 env2 p2  in
                         (match uu____6024 with
                          | (loc2,env3,uu____6071,pat,ans,uu____6074) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5882 with
             | (loc1,env2,annots,args1) ->
                 let args2 = FStar_List.rev args1  in
                 let l =
                   if dep1
                   then
                     FStar_Parser_Const.mk_dtuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                   else
                     FStar_Parser_Const.mk_tuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                    in
                 let constr =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                    in
                 let l1 =
                   match constr.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                   | uu____6240 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6243 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6243, annots, false))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange
               in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____6324  ->
                      match uu____6324 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6354  ->
                      match uu____6354 with
                      | (f,uu____6360) ->
                          let uu____6361 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6387  ->
                                    match uu____6387 with
                                    | (g,uu____6394) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6361 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6400,p2) ->
                               p2)))
               in
            let app =
              let uu____6407 =
                let uu____6408 =
                  let uu____6415 =
                    let uu____6416 =
                      let uu____6417 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6417  in
                    FStar_Parser_AST.mk_pattern uu____6416
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6415, args)  in
                FStar_Parser_AST.PatApp uu____6408  in
              FStar_Parser_AST.mk_pattern uu____6407
                p1.FStar_Parser_AST.prange
               in
            let uu____6420 = aux loc env1 app  in
            (match uu____6420 with
             | (env2,e,b,p2,annots,uu____6466) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6506 =
                         let uu____6507 =
                           let uu____6521 =
                             let uu___293_6522 = fv  in
                             let uu____6523 =
                               let uu____6526 =
                                 let uu____6527 =
                                   let uu____6534 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6534)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6527
                                  in
                               FStar_Pervasives_Native.Some uu____6526  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___293_6522.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___293_6522.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6523
                             }  in
                           (uu____6521, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6507  in
                       FStar_All.pipe_left pos uu____6506
                   | uu____6560 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6646 = aux' true loc env1 p2  in
            (match uu____6646 with
             | (loc1,env2,var,p3,ans,uu____6690) ->
                 let uu____6705 =
                   FStar_List.fold_left
                     (fun uu____6754  ->
                        fun p4  ->
                          match uu____6754 with
                          | (loc2,env3,ps1) ->
                              let uu____6819 = aux' true loc2 env3 p4  in
                              (match uu____6819 with
                               | (loc3,env4,uu____6860,p5,ans1,uu____6863) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6705 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7024 ->
            let uu____7025 = aux' true loc env1 p1  in
            (match uu____7025 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7122 = aux_maybe_or env p  in
      match uu____7122 with
      | (env1,b,pats) ->
          ((let uu____7177 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7177
              p.FStar_Parser_AST.prange);
           (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        let mklet x ty tacopt =
          let uu____7250 =
            let uu____7251 =
              let uu____7262 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7262, (ty, tacopt))  in
            LetBinder uu____7251  in
          (env, uu____7250, [])  in
        let op_to_ident x =
          let uu____7279 =
            let uu____7285 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7285, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7279  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7307 = op_to_ident x  in
              mklet uu____7307 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7309) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7315;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7331 = op_to_ident x  in
              let uu____7332 = desugar_term env t  in
              mklet uu____7331 uu____7332 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7334);
                 FStar_Parser_AST.prange = uu____7335;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7355 = desugar_term env t  in
              mklet x uu____7355 tacopt1
          | uu____7356 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7369 = desugar_data_pat env p  in
           match uu____7369 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7398;
                      FStar_Syntax_Syntax.p = uu____7399;_},uu____7400)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7413;
                      FStar_Syntax_Syntax.p = uu____7414;_},uu____7415)::[]
                     -> []
                 | uu____7428 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7436  ->
    fun env  ->
      fun pat  ->
        let uu____7440 = desugar_data_pat env pat  in
        match uu____7440 with | (env1,uu____7456,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7478 = desugar_term_aq env e  in
      match uu____7478 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7497 = desugar_typ_aq env e  in
      match uu____7497 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7507  ->
        fun range  ->
          match uu____7507 with
          | (signedness,width) ->
              let tnm =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7529 =
                  let uu____7531 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7531  in
                if uu____7529
                then
                  let uu____7534 =
                    let uu____7540 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7540)  in
                  FStar_Errors.log_issue range uu____7534
                else ());
               (let private_intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat ".__"
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat "."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7561 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7561 range  in
                let lid1 =
                  let uu____7565 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7565 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7575 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7575 range  in
                           let private_fv =
                             let uu____7577 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7577 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___294_7578 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___294_7578.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___294_7578.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7579 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7583 =
                        let uu____7589 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7589)
                         in
                      FStar_Errors.raise_error uu____7583 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7609 =
                  let uu____7616 =
                    let uu____7617 =
                      let uu____7634 =
                        let uu____7645 =
                          let uu____7654 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7654)  in
                        [uu____7645]  in
                      (lid1, uu____7634)  in
                    FStar_Syntax_Syntax.Tm_app uu____7617  in
                  FStar_Syntax_Syntax.mk uu____7616  in
                uu____7609 FStar_Pervasives_Native.None range))

and (desugar_name :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____7705 =
              let uu____7712 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7712 l  in
            match uu____7705 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7764;
                              FStar_Syntax_Syntax.vars = uu____7765;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7793 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7793 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7809 =
                                 let uu____7810 =
                                   let uu____7813 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7813  in
                                 uu____7810.FStar_Syntax_Syntax.n  in
                               match uu____7809 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7836))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7843 -> msg
                             else msg  in
                           let uu____7846 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7846
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7851 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7851 " is deprecated"  in
                           let uu____7854 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7854
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7856 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7871 =
          let uu____7872 = unparen t  in uu____7872.FStar_Parser_AST.tm  in
        match uu____7871 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7873; FStar_Ident.ident = uu____7874;
              FStar_Ident.nsstr = uu____7875; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7880 ->
            let uu____7881 =
              let uu____7887 =
                let uu____7889 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7889  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7887)  in
            FStar_Errors.raise_error uu____7881 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___295_7976 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___295_7976.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___295_7976.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7979 =
          let uu____7980 = unparen top  in uu____7980.FStar_Parser_AST.tm  in
        match uu____7979 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7985 ->
            let uu____7994 = desugar_formula env top  in (uu____7994, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8003 = desugar_formula env t  in (uu____8003, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8012 = desugar_formula env t  in (uu____8012, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8039 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8039, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8041 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8041, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8050 =
                let uu____8051 =
                  let uu____8058 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8058, args)  in
                FStar_Parser_AST.Op uu____8051  in
              FStar_Parser_AST.mk_term uu____8050 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8063 =
              let uu____8064 =
                let uu____8065 =
                  let uu____8072 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8072, [e])  in
                FStar_Parser_AST.Op uu____8065  in
              FStar_Parser_AST.mk_term uu____8064 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8063
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8084 = FStar_Ident.text_of_id op_star  in
             uu____8084 = "*") &&
              (let uu____8089 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8089 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8106;_},t1::t2::[])
                  when
                  let uu____8112 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8112 FStar_Option.isNone ->
                  let uu____8119 = flatten1 t1  in
                  FStar_List.append uu____8119 [t2]
              | uu____8122 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___296_8127 = top  in
              let uu____8128 =
                let uu____8129 =
                  let uu____8140 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____8140, rhs)  in
                FStar_Parser_AST.Sum uu____8129  in
              {
                FStar_Parser_AST.tm = uu____8128;
                FStar_Parser_AST.range =
                  (uu___296_8127.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___296_8127.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8158 =
              let uu____8159 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8159  in
            (uu____8158, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8165 =
              let uu____8171 =
                let uu____8173 =
                  let uu____8175 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____8175 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____8173  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8171)  in
            FStar_Errors.raise_error uu____8165 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8190 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8190 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8197 =
                   let uu____8203 =
                     let uu____8205 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____8205
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8203)
                    in
                 FStar_Errors.raise_error uu____8197
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8220 =
                     let uu____8245 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8307 = desugar_term_aq env t  in
                               match uu____8307 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8245 FStar_List.unzip  in
                   (match uu____8220 with
                    | (args1,aqs) ->
                        let uu____8440 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8440, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8457)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8474 =
              let uu___297_8475 = top  in
              let uu____8476 =
                let uu____8477 =
                  let uu____8484 =
                    let uu___298_8485 = top  in
                    let uu____8486 =
                      let uu____8487 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8487  in
                    {
                      FStar_Parser_AST.tm = uu____8486;
                      FStar_Parser_AST.range =
                        (uu___298_8485.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___298_8485.FStar_Parser_AST.level)
                    }  in
                  (uu____8484, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8477  in
              {
                FStar_Parser_AST.tm = uu____8476;
                FStar_Parser_AST.range =
                  (uu___297_8475.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___297_8475.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8474
        | FStar_Parser_AST.Construct (n1,(a,uu____8495)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8515 =
                let uu___299_8516 = top  in
                let uu____8517 =
                  let uu____8518 =
                    let uu____8525 =
                      let uu___300_8526 = top  in
                      let uu____8527 =
                        let uu____8528 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8528  in
                      {
                        FStar_Parser_AST.tm = uu____8527;
                        FStar_Parser_AST.range =
                          (uu___300_8526.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___300_8526.FStar_Parser_AST.level)
                      }  in
                    (uu____8525, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8518  in
                {
                  FStar_Parser_AST.tm = uu____8517;
                  FStar_Parser_AST.range =
                    (uu___299_8516.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___299_8516.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8515))
        | FStar_Parser_AST.Construct (n1,(a,uu____8536)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8553 =
              let uu___301_8554 = top  in
              let uu____8555 =
                let uu____8556 =
                  let uu____8563 =
                    let uu___302_8564 = top  in
                    let uu____8565 =
                      let uu____8566 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8566  in
                    {
                      FStar_Parser_AST.tm = uu____8565;
                      FStar_Parser_AST.range =
                        (uu___302_8564.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___302_8564.FStar_Parser_AST.level)
                    }  in
                  (uu____8563, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8556  in
              {
                FStar_Parser_AST.tm = uu____8555;
                FStar_Parser_AST.range =
                  (uu___301_8554.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___301_8554.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8553
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8572; FStar_Ident.ident = uu____8573;
              FStar_Ident.nsstr = uu____8574; FStar_Ident.str = "Type0";_}
            ->
            let uu____8579 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8579, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8580; FStar_Ident.ident = uu____8581;
              FStar_Ident.nsstr = uu____8582; FStar_Ident.str = "Type";_}
            ->
            let uu____8587 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8587, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8588; FStar_Ident.ident = uu____8589;
               FStar_Ident.nsstr = uu____8590; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8610 =
              let uu____8611 =
                let uu____8612 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8612  in
              mk1 uu____8611  in
            (uu____8610, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8613; FStar_Ident.ident = uu____8614;
              FStar_Ident.nsstr = uu____8615; FStar_Ident.str = "Effect";_}
            ->
            let uu____8620 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8620, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8621; FStar_Ident.ident = uu____8622;
              FStar_Ident.nsstr = uu____8623; FStar_Ident.str = "True";_}
            ->
            let uu____8628 =
              let uu____8629 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8629
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8628, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8630; FStar_Ident.ident = uu____8631;
              FStar_Ident.nsstr = uu____8632; FStar_Ident.str = "False";_}
            ->
            let uu____8637 =
              let uu____8638 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8638
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8637, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8641;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8644 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8644 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8653 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8653, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8655 =
                    let uu____8657 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8657 txt
                     in
                  failwith uu____8655))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8666 = desugar_name mk1 setpos env true l  in
              (uu____8666, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8670 = desugar_name mk1 setpos env true l  in
              (uu____8670, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8683 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8683 with
                | FStar_Pervasives_Native.Some uu____8693 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8701 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8701 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8719 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8740 =
                    let uu____8741 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8741  in
                  (uu____8740, noaqs)
              | uu____8742 ->
                  let uu____8750 =
                    let uu____8756 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8756)  in
                  FStar_Errors.raise_error uu____8750
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8766 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8766 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8773 =
                    let uu____8779 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8779)
                     in
                  FStar_Errors.raise_error uu____8773
                    top.FStar_Parser_AST.range
              | uu____8787 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8791 = desugar_name mk1 setpos env true lid'  in
                  (uu____8791, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8808 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8808 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8827 ->
                       let uu____8834 =
                         FStar_Util.take
                           (fun uu____8858  ->
                              match uu____8858 with
                              | (uu____8864,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8834 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8909 =
                              let uu____8934 =
                                FStar_List.map
                                  (fun uu____8977  ->
                                     match uu____8977 with
                                     | (t,imp) ->
                                         let uu____8994 =
                                           desugar_term_aq env t  in
                                         (match uu____8994 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8934
                                FStar_List.unzip
                               in
                            (match uu____8909 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9137 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9137, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9156 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9156 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9167 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___256_9195  ->
                 match uu___256_9195 with
                 | FStar_Util.Inr uu____9201 -> true
                 | uu____9203 -> false) binders
            ->
            let terms =
              let uu____9212 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___257_9229  ->
                        match uu___257_9229 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9235 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9212 [t]  in
            let uu____9237 =
              let uu____9262 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9319 = desugar_typ_aq env t1  in
                        match uu____9319 with
                        | (t',aq) ->
                            let uu____9330 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9330, aq)))
                 in
              FStar_All.pipe_right uu____9262 FStar_List.unzip  in
            (match uu____9237 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9440 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9440
                    in
                 let uu____9449 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9449, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9476 =
              let uu____9493 =
                let uu____9500 =
                  let uu____9507 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9507]  in
                FStar_List.append binders uu____9500  in
              FStar_List.fold_left
                (fun uu____9560  ->
                   fun b  ->
                     match uu____9560 with
                     | (env1,tparams,typs) ->
                         let uu____9621 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9636 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9636)
                            in
                         (match uu____9621 with
                          | (xopt,t1) ->
                              let uu____9661 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9670 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9670)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9661 with
                               | (env2,x) ->
                                   let uu____9690 =
                                     let uu____9693 =
                                       let uu____9696 =
                                         let uu____9697 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9697
                                          in
                                       [uu____9696]  in
                                     FStar_List.append typs uu____9693  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___303_9723 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___303_9723.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___303_9723.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9690)))) (env, [], []) uu____9493
               in
            (match uu____9476 with
             | (env1,uu____9751,targs) ->
                 let tup =
                   let uu____9774 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9774
                    in
                 let uu____9775 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9775, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9794 = uncurry binders t  in
            (match uu____9794 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___258_9838 =
                   match uu___258_9838 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9855 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9855
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9879 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9879 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9912 = aux env [] bs  in (uu____9912, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9921 = desugar_binder env b  in
            (match uu____9921 with
             | (FStar_Pervasives_Native.None ,uu____9932) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9947 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9947 with
                  | ((x,uu____9963),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9976 =
                        let uu____9977 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9977  in
                      (uu____9976, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10056 = FStar_Util.set_is_empty i  in
                    if uu____10056
                    then
                      let uu____10061 = FStar_Util.set_union acc set1  in
                      aux uu____10061 sets2
                    else
                      (let uu____10066 =
                         let uu____10067 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10067  in
                       FStar_Pervasives_Native.Some uu____10066)
                 in
              let uu____10070 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10070 sets  in
            ((let uu____10074 = check_disjoint bvss  in
              match uu____10074 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10078 =
                    let uu____10084 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10084)
                     in
                  let uu____10088 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10078 uu____10088);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10096 =
                FStar_List.fold_left
                  (fun uu____10116  ->
                     fun pat  ->
                       match uu____10116 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10142,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10152 =
                                  let uu____10155 = free_type_vars env1 t  in
                                  FStar_List.append uu____10155 ftvs  in
                                (env1, uu____10152)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10160,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10171 =
                                  let uu____10174 = free_type_vars env1 t  in
                                  let uu____10177 =
                                    let uu____10180 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10180 ftvs  in
                                  FStar_List.append uu____10174 uu____10177
                                   in
                                (env1, uu____10171)
                            | uu____10185 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10096 with
              | (uu____10194,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10206 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a  ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range))
                       in
                    FStar_List.append uu____10206 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___259_10263 =
                    match uu___259_10263 with
                    | [] ->
                        let uu____10290 = desugar_term_aq env1 body  in
                        (match uu____10290 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10327 =
                                       let uu____10328 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10328
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10327
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____10397 =
                               let uu____10400 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10400  in
                             (uu____10397, aq))
                    | p::rest ->
                        let uu____10415 = desugar_binding_pat env1 p  in
                        (match uu____10415 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10449)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10464 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10473 =
                               match b with
                               | LetBinder uu____10514 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10583) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10637 =
                                           let uu____10646 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10646, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10637
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10708,uu____10709) ->
                                              let tup2 =
                                                let uu____10711 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10711
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10716 =
                                                  let uu____10723 =
                                                    let uu____10724 =
                                                      let uu____10741 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10744 =
                                                        let uu____10755 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10764 =
                                                          let uu____10775 =
                                                            let uu____10784 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10784
                                                             in
                                                          [uu____10775]  in
                                                        uu____10755 ::
                                                          uu____10764
                                                         in
                                                      (uu____10741,
                                                        uu____10744)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10724
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10723
                                                   in
                                                uu____10716
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10835 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10835
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10886,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10888,pats)) ->
                                              let tupn =
                                                let uu____10933 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10933
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10946 =
                                                  let uu____10947 =
                                                    let uu____10964 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10967 =
                                                      let uu____10978 =
                                                        let uu____10989 =
                                                          let uu____10998 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10998
                                                           in
                                                        [uu____10989]  in
                                                      FStar_List.append args
                                                        uu____10978
                                                       in
                                                    (uu____10964,
                                                      uu____10967)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10947
                                                   in
                                                mk1 uu____10946  in
                                              let p2 =
                                                let uu____11046 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11046
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11093 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10473 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11187,uu____11188,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11210 =
                let uu____11211 = unparen e  in
                uu____11211.FStar_Parser_AST.tm  in
              match uu____11210 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11221 ->
                  let uu____11222 = desugar_term_aq env e  in
                  (match uu____11222 with
                   | (head1,aq) ->
                       let uu____11235 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11235, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11242 ->
            let rec aux args aqs e =
              let uu____11319 =
                let uu____11320 = unparen e  in
                uu____11320.FStar_Parser_AST.tm  in
              match uu____11319 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11338 = desugar_term_aq env t  in
                  (match uu____11338 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11386 ->
                  let uu____11387 = desugar_term_aq env e  in
                  (match uu____11387 with
                   | (head1,aq) ->
                       let uu____11408 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11408, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr
               in
            let uu____11471 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11471
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____11523 = desugar_term_aq env t  in
            (match uu____11523 with
             | (tm,s) ->
                 let uu____11534 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11534, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11540 =
              let uu____11553 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11553 then desugar_typ_aq else desugar_term_aq  in
            uu____11540 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11612 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11755  ->
                        match uu____11755 with
                        | (attr_opt,(p,def)) ->
                            let uu____11813 = is_app_pattern p  in
                            if uu____11813
                            then
                              let uu____11846 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11846, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11929 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11929, def1)
                               | uu____11974 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12012);
                                           FStar_Parser_AST.prange =
                                             uu____12013;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12062 =
                                            let uu____12083 =
                                              let uu____12088 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12088  in
                                            (uu____12083, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12062, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12180) ->
                                        if top_level
                                        then
                                          let uu____12216 =
                                            let uu____12237 =
                                              let uu____12242 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12242  in
                                            (uu____12237, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12216, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12333 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12366 =
                FStar_List.fold_left
                  (fun uu____12439  ->
                     fun uu____12440  ->
                       match (uu____12439, uu____12440) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12548,uu____12549),uu____12550))
                           ->
                           let uu____12667 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12693 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12693 with
                                  | (env2,xx) ->
                                      let uu____12712 =
                                        let uu____12715 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12715 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12712))
                             | FStar_Util.Inr l ->
                                 let uu____12723 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12723, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12667 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12366 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12871 =
                    match uu____12871 with
                    | (attrs_opt,(uu____12907,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let pos = def.FStar_Parser_AST.range  in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some (t,tacopt) ->
                              let t1 =
                                let uu____12995 = is_comp_type env1 t  in
                                if uu____12995
                                then
                                  ((let uu____12999 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13009 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13009))
                                       in
                                    match uu____12999 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13016 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13019 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13019))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13016
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13030 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____13045 =
                                let uu____13046 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13046
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13045
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l
                           in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2,
                            pos)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let uu____13127 = desugar_term_aq env' body  in
                  (match uu____13127 with
                   | (body1,aq) ->
                       let uu____13140 =
                         let uu____13143 =
                           let uu____13144 =
                             let uu____13158 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13158)  in
                           FStar_Syntax_Syntax.Tm_let uu____13144  in
                         FStar_All.pipe_left mk1 uu____13143  in
                       (uu____13140, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13233 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13233 with
              | (env1,binder,pat1) ->
                  let uu____13255 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13281 = desugar_term_aq env1 t2  in
                        (match uu____13281 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13295 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13295
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13296 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13296, aq))
                    | LocalBinder (x,uu____13329) ->
                        let uu____13330 = desugar_term_aq env1 t2  in
                        (match uu____13330 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13344;
                                    FStar_Syntax_Syntax.p = uu____13345;_},uu____13346)::[]
                                   -> body1
                               | uu____13359 ->
                                   let uu____13362 =
                                     let uu____13369 =
                                       let uu____13370 =
                                         let uu____13393 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13396 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13393, uu____13396)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13370
                                        in
                                     FStar_Syntax_Syntax.mk uu____13369  in
                                   uu____13362 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13436 =
                               let uu____13439 =
                                 let uu____13440 =
                                   let uu____13454 =
                                     let uu____13457 =
                                       let uu____13458 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13458]  in
                                     FStar_Syntax_Subst.close uu____13457
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13454)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13440  in
                               FStar_All.pipe_left mk1 uu____13439  in
                             (uu____13436, aq))
                     in
                  (match uu____13255 with | (tm,aq) -> (tm, aq))
               in
            let uu____13520 = FStar_List.hd lbs  in
            (match uu____13520 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13564 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13564
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13580 =
                let uu____13581 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13581  in
              mk1 uu____13580  in
            let uu____13582 = desugar_term_aq env t1  in
            (match uu____13582 with
             | (t1',aq1) ->
                 let uu____13593 = desugar_term_aq env t2  in
                 (match uu____13593 with
                  | (t2',aq2) ->
                      let uu____13604 = desugar_term_aq env t3  in
                      (match uu____13604 with
                       | (t3',aq3) ->
                           let uu____13615 =
                             let uu____13616 =
                               let uu____13617 =
                                 let uu____13640 =
                                   let uu____13657 =
                                     let uu____13672 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13672,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13686 =
                                     let uu____13703 =
                                       let uu____13718 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13718,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13703]  in
                                   uu____13657 :: uu____13686  in
                                 (t1', uu____13640)  in
                               FStar_Syntax_Syntax.Tm_match uu____13617  in
                             mk1 uu____13616  in
                           (uu____13615, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____13914 =
              match uu____13914 with
              | (pat,wopt,b) ->
                  let uu____13936 = desugar_match_pat env pat  in
                  (match uu____13936 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13967 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13967
                          in
                       let uu____13972 = desugar_term_aq env1 b  in
                       (match uu____13972 with
                        | (b1,aq) ->
                            let uu____13985 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13985, aq)))
               in
            let uu____13990 = desugar_term_aq env e  in
            (match uu____13990 with
             | (e1,aq) ->
                 let uu____14001 =
                   let uu____14032 =
                     let uu____14065 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14065 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14032
                     (fun uu____14283  ->
                        match uu____14283 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14001 with
                  | (brs,aqs) ->
                      let uu____14502 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14502, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14536 =
              let uu____14557 = is_comp_type env t  in
              if uu____14557
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14612 = desugar_term_aq env t  in
                 match uu____14612 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14536 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14704 = desugar_term_aq env e  in
                 (match uu____14704 with
                  | (e1,aq) ->
                      let uu____14715 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14715, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14754,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14797 = FStar_List.hd fields  in
              match uu____14797 with | (f,uu____14809) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14855  ->
                        match uu____14855 with
                        | (g,uu____14862) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14869,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14883 =
                         let uu____14889 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14889)
                          in
                       FStar_Errors.raise_error uu____14883
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____14900 =
                    let uu____14911 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14942  ->
                              match uu____14942 with
                              | (f,uu____14952) ->
                                  let uu____14953 =
                                    let uu____14954 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____14954
                                     in
                                  (uu____14953, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14911)  in
                  FStar_Parser_AST.Construct uu____14900
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____14972 =
                      let uu____14973 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____14973  in
                    FStar_Parser_AST.mk_term uu____14972
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____14975 =
                      let uu____14988 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15018  ->
                                match uu____15018 with
                                | (f,uu____15028) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____14988)  in
                    FStar_Parser_AST.Record uu____14975  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15088 = desugar_term_aq env recterm1  in
            (match uu____15088 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15104;
                         FStar_Syntax_Syntax.vars = uu____15105;_},args)
                      ->
                      let uu____15131 =
                        let uu____15132 =
                          let uu____15133 =
                            let uu____15150 =
                              let uu____15153 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15154 =
                                let uu____15157 =
                                  let uu____15158 =
                                    let uu____15165 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15165)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15158
                                   in
                                FStar_Pervasives_Native.Some uu____15157  in
                              FStar_Syntax_Syntax.fvar uu____15153
                                FStar_Syntax_Syntax.delta_constant
                                uu____15154
                               in
                            (uu____15150, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15133  in
                        FStar_All.pipe_left mk1 uu____15132  in
                      (uu____15131, s)
                  | uu____15194 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15198 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15198 with
              | (constrname,is_rec) ->
                  let uu____15217 = desugar_term_aq env e  in
                  (match uu____15217 with
                   | (e1,s) ->
                       let projname =
                         FStar_Syntax_Util.mk_field_projector_name_from_ident
                           constrname f.FStar_Ident.ident
                          in
                       let qual =
                         if is_rec
                         then
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.Record_projector
                                (constrname, (f.FStar_Ident.ident)))
                         else FStar_Pervasives_Native.None  in
                       let uu____15237 =
                         let uu____15238 =
                           let uu____15239 =
                             let uu____15256 =
                               let uu____15259 =
                                 let uu____15260 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15260
                                  in
                               FStar_Syntax_Syntax.fvar uu____15259
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15262 =
                               let uu____15273 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15273]  in
                             (uu____15256, uu____15262)  in
                           FStar_Syntax_Syntax.Tm_app uu____15239  in
                         FStar_All.pipe_left mk1 uu____15238  in
                       (uu____15237, s))))
        | FStar_Parser_AST.NamedTyp (uu____15310,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15320 =
              let uu____15321 = FStar_Syntax_Subst.compress tm  in
              uu____15321.FStar_Syntax_Syntax.n  in
            (match uu____15320 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15329 =
                   let uu___304_15330 =
                     let uu____15331 =
                       let uu____15333 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15333  in
                     FStar_Syntax_Util.exp_string uu____15331  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___304_15330.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___304_15330.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15329, noaqs)
             | uu____15334 ->
                 let uu____15335 =
                   let uu____15341 =
                     let uu____15343 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____15343
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15341)  in
                 FStar_Errors.raise_error uu____15335
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15352 = desugar_term_aq env e  in
            (match uu____15352 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15364 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15364, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15369 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15370 =
              let uu____15371 =
                let uu____15378 = desugar_term env e  in (bv, uu____15378)
                 in
              [uu____15371]  in
            (uu____15369, uu____15370)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15403 =
              let uu____15404 =
                let uu____15405 =
                  let uu____15412 = desugar_term env e  in (uu____15412, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15405  in
              FStar_All.pipe_left mk1 uu____15404  in
            (uu____15403, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____15441 =
                let uu____15442 =
                  let uu____15449 =
                    let uu____15450 =
                      let uu____15451 =
                        let uu____15460 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15473 =
                          let uu____15474 =
                            let uu____15475 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15475  in
                          FStar_Parser_AST.mk_term uu____15474
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15460, uu____15473,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15451  in
                    FStar_Parser_AST.mk_term uu____15450
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15449)  in
                FStar_Parser_AST.Abs uu____15442  in
              FStar_Parser_AST.mk_term uu____15441
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let e1 =
              FStar_List.fold_left
                (fun e1  ->
                   fun uu____15521  ->
                     match uu____15521 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____15525 =
                           let uu____15532 =
                             let uu____15537 = eta_and_annot rel2  in
                             (uu____15537, FStar_Parser_AST.Nothing)  in
                           let uu____15538 =
                             let uu____15545 =
                               let uu____15552 =
                                 let uu____15557 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____15557, FStar_Parser_AST.Nothing)  in
                               let uu____15558 =
                                 let uu____15565 =
                                   let uu____15570 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____15570, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____15565]  in
                               uu____15552 :: uu____15558  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____15545
                              in
                           uu____15532 :: uu____15538  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____15525
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____15592 =
                let uu____15599 =
                  let uu____15604 = FStar_Parser_AST.thunk e1  in
                  (uu____15604, FStar_Parser_AST.Nothing)  in
                [uu____15599]  in
              FStar_Parser_AST.mkApp finish1 uu____15592
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____15613 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15614 = desugar_formula env top  in
            (uu____15614, noaqs)
        | uu____15615 ->
            let uu____15616 =
              let uu____15622 =
                let uu____15624 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____15624  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15622)  in
            FStar_Errors.raise_error uu____15616 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15634 -> false
    | uu____15644 -> true

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____15682  ->
              match uu____15682 with
              | (a,imp) ->
                  let uu____15695 = desugar_term env a  in
                  arg_withimp_e imp uu____15695))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____15732 =
            match uu____15732 with
            | (t1,uu____15739) ->
                let uu____15740 =
                  let uu____15741 = unparen t1  in
                  uu____15741.FStar_Parser_AST.tm  in
                (match uu____15740 with
                 | FStar_Parser_AST.Requires uu____15743 -> true
                 | uu____15752 -> false)
             in
          let is_ensures uu____15764 =
            match uu____15764 with
            | (t1,uu____15771) ->
                let uu____15772 =
                  let uu____15773 = unparen t1  in
                  uu____15773.FStar_Parser_AST.tm  in
                (match uu____15772 with
                 | FStar_Parser_AST.Ensures uu____15775 -> true
                 | uu____15784 -> false)
             in
          let is_app head1 uu____15802 =
            match uu____15802 with
            | (t1,uu____15810) ->
                let uu____15811 =
                  let uu____15812 = unparen t1  in
                  uu____15812.FStar_Parser_AST.tm  in
                (match uu____15811 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15815;
                        FStar_Parser_AST.level = uu____15816;_},uu____15817,uu____15818)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15820 -> false)
             in
          let is_smt_pat uu____15832 =
            match uu____15832 with
            | (t1,uu____15839) ->
                let uu____15840 =
                  let uu____15841 = unparen t1  in
                  uu____15841.FStar_Parser_AST.tm  in
                (match uu____15840 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____15845);
                               FStar_Parser_AST.range = uu____15846;
                               FStar_Parser_AST.level = uu____15847;_},uu____15848)::uu____15849::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____15898;
                               FStar_Parser_AST.level = uu____15899;_},uu____15900)::uu____15901::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____15934 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____15969 = head_and_args t1  in
            match uu____15969 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
                     let unit_tm =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let nil_pat =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                           t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                         FStar_Parser_AST.Nothing)
                        in
                     let req_true =
                       let req =
                         FStar_Parser_AST.Requires
                           ((FStar_Parser_AST.mk_term
                               (FStar_Parser_AST.Name
                                  FStar_Parser_Const.true_lid)
                               t1.FStar_Parser_AST.range
                               FStar_Parser_AST.Formula),
                             FStar_Pervasives_Native.None)
                          in
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let thunk_ens uu____16062 =
                       match uu____16062 with
                       | (e,i) ->
                           let uu____16073 = FStar_Parser_AST.thunk e  in
                           (uu____16073, i)
                        in
                     let fail_lemma uu____16085 =
                       let expected_one_of =
                         ["Lemma post";
                         "Lemma (ensures post)";
                         "Lemma (requires pre) (ensures post)";
                         "Lemma post [SMTPat ...]";
                         "Lemma (ensures post) [SMTPat ...]";
                         "Lemma (ensures post) (decreases d)";
                         "Lemma (ensures post) (decreases d) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d)";
                         "Lemma (requires pre) (ensures post) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                          in
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.strcat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg)) t1.FStar_Parser_AST.range
                        in
                     let args1 =
                       match args with
                       | [] -> fail_lemma ()
                       | req::[] when is_requires req -> fail_lemma ()
                       | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                       | dec::[] when is_decreases dec -> fail_lemma ()
                       | ens::[] ->
                           let uu____16191 =
                             let uu____16198 =
                               let uu____16205 = thunk_ens ens  in
                               [uu____16205; nil_pat]  in
                             req_true :: uu____16198  in
                           unit_tm :: uu____16191
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16252 =
                             let uu____16259 =
                               let uu____16266 = thunk_ens ens  in
                               [uu____16266; nil_pat]  in
                             req :: uu____16259  in
                           unit_tm :: uu____16252
                       | ens::smtpat::[] when
                           (((let uu____16315 = is_requires ens  in
                              Prims.op_Negation uu____16315) &&
                               (let uu____16318 = is_smt_pat ens  in
                                Prims.op_Negation uu____16318))
                              &&
                              (let uu____16321 = is_decreases ens  in
                               Prims.op_Negation uu____16321))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16323 =
                             let uu____16330 =
                               let uu____16337 = thunk_ens ens  in
                               [uu____16337; smtpat]  in
                             req_true :: uu____16330  in
                           unit_tm :: uu____16323
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16384 =
                             let uu____16391 =
                               let uu____16398 = thunk_ens ens  in
                               [uu____16398; nil_pat; dec]  in
                             req_true :: uu____16391  in
                           unit_tm :: uu____16384
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16458 =
                             let uu____16465 =
                               let uu____16472 = thunk_ens ens  in
                               [uu____16472; smtpat; dec]  in
                             req_true :: uu____16465  in
                           unit_tm :: uu____16458
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16532 =
                             let uu____16539 =
                               let uu____16546 = thunk_ens ens  in
                               [uu____16546; nil_pat; dec]  in
                             req :: uu____16539  in
                           unit_tm :: uu____16532
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16606 =
                             let uu____16613 =
                               let uu____16620 = thunk_ens ens  in
                               [uu____16620; smtpat]  in
                             req :: uu____16613  in
                           unit_tm :: uu____16606
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16685 =
                             let uu____16692 =
                               let uu____16699 = thunk_ens ens  in
                               [uu____16699; dec; smtpat]  in
                             req :: uu____16692  in
                           unit_tm :: uu____16685
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16761 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16761, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16789 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16789
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16792 =
                       let uu____16799 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16799, [])  in
                     (uu____16792, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16817 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16817
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16820 =
                       let uu____16827 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16827, [])  in
                     (uu____16820, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____16849 =
                       let uu____16856 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16856, [])  in
                     (uu____16849, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16879 when allow_type_promotion ->
                     let default_effect =
                       let uu____16881 = FStar_Options.ml_ish ()  in
                       if uu____16881
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16887 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____16887
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____16894 =
                       let uu____16901 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16901, [])  in
                     (uu____16894, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16924 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____16943 = pre_process_comp_typ t  in
          match uu____16943 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____16995 =
                    let uu____17001 =
                      let uu____17003 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17003
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17001)
                     in
                  fail1 uu____16995)
               else ();
               (let is_universe uu____17019 =
                  match uu____17019 with
                  | (uu____17025,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17027 = FStar_Util.take is_universe args  in
                match uu____17027 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17086  ->
                           match uu____17086 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17093 =
                      let uu____17108 = FStar_List.hd args1  in
                      let uu____17117 = FStar_List.tl args1  in
                      (uu____17108, uu____17117)  in
                    (match uu____17093 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17172 =
                           let is_decrease uu____17211 =
                             match uu____17211 with
                             | (t1,uu____17222) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17233;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17234;_},uu____17235::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17274 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17172 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17391  ->
                                        match uu____17391 with
                                        | (t1,uu____17401) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17410,(arg,uu____17412)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17451 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17472 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17484 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17484
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17491 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17491
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags1 =
                                      let uu____17501 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17501
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17508 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17508
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17515 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17515
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17522 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17522
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags2 =
                                      FStar_List.append flags1 cattributes
                                       in
                                    let rest3 =
                                      let uu____17543 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17543
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv
                                                    FStar_Parser_Const.nil_lid
                                                  ->
                                                  let nil =
                                                    FStar_Syntax_Syntax.mk_Tm_uinst
                                                      pat
                                                      [FStar_Syntax_Syntax.U_zero]
                                                     in
                                                  let pattern =
                                                    let uu____17634 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17634
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    FStar_Pervasives_Native.None
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____17655 -> pat  in
                                            let uu____17656 =
                                              let uu____17667 =
                                                let uu____17678 =
                                                  let uu____17687 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17687, aq)  in
                                                [uu____17678]  in
                                              ens :: uu____17667  in
                                            req :: uu____17656
                                        | uu____17728 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags2
                                             decreases_clause)
                                      }))))))

and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____17760 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___305_17782 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___305_17782.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___305_17782.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___306_17824 = b  in
             {
               FStar_Parser_AST.b = (uu___306_17824.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___306_17824.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___306_17824.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____17887 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____17887)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17900 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17900 with
             | (env1,a1) ->
                 let a2 =
                   let uu___307_17910 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___307_17910.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___307_17910.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____17936 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____17950 =
                     let uu____17953 =
                       let uu____17954 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____17954]  in
                     no_annot_abs uu____17953 body2  in
                   FStar_All.pipe_left setpos uu____17950  in
                 let uu____17975 =
                   let uu____17976 =
                     let uu____17993 =
                       let uu____17996 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____17996
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____17998 =
                       let uu____18009 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18009]  in
                     (uu____17993, uu____17998)  in
                   FStar_Syntax_Syntax.Tm_app uu____17976  in
                 FStar_All.pipe_left mk1 uu____17975)
        | uu____18048 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18129 = q (rest, pats, body)  in
              let uu____18136 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18129 uu____18136
                FStar_Parser_AST.Formula
               in
            let uu____18137 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18137 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18146 -> failwith "impossible"  in
      let uu____18150 =
        let uu____18151 = unparen f  in uu____18151.FStar_Parser_AST.tm  in
      match uu____18150 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18164,uu____18165) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18177,uu____18178) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18210 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18210
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18246 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18246
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18290 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18295 =
        FStar_List.fold_left
          (fun uu____18328  ->
             fun b  ->
               match uu____18328 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___308_18372 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___308_18372.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___308_18372.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___308_18372.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18387 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18387 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___309_18405 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___309_18405.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___309_18405.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18406 =
                               let uu____18413 =
                                 let uu____18418 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18418)  in
                               uu____18413 :: out  in
                             (env2, uu____18406))
                    | uu____18429 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18295 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____18502 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18502)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18507 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18507)
      | FStar_Parser_AST.TVariable x ->
          let uu____18511 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18511)
      | FStar_Parser_AST.NoName t ->
          let uu____18515 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18515)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___260_18523  ->
        match uu___260_18523 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18545 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18545, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18562 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18562 with
             | (env1,a1) ->
                 let uu____18579 =
                   let uu____18586 = trans_aqual env1 imp  in
                   ((let uu___310_18592 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___310_18592.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___310_18592.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18586)
                    in
                 (uu____18579, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___261_18600  ->
      match uu___261_18600 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18604 =
            let uu____18605 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18605  in
          FStar_Pervasives_Native.Some uu____18604
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18621) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18623) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18626 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18644 = binder_ident b  in
         FStar_Common.list_of_option uu____18644) bs
  
let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___262_18681  ->
                  match uu___262_18681 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18686 -> false))
           in
        let quals2 q =
          let uu____18700 =
            (let uu____18704 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18704) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18700
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18721 = FStar_Ident.range_of_lid disc_name  in
                let uu____18722 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18721;
                  FStar_Syntax_Syntax.sigquals = uu____18722;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____18762 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18800  ->
                        match uu____18800 with
                        | (x,uu____18811) ->
                            let uu____18816 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18816 with
                             | (field_name,uu____18824) ->
                                 let only_decl =
                                   ((let uu____18829 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18829)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18831 =
                                        let uu____18833 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18833.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18831)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____18851 =
                                       FStar_List.filter
                                         (fun uu___263_18855  ->
                                            match uu___263_18855 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____18858 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____18851
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___264_18873  ->
                                             match uu___264_18873 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____18878 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____18881 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____18881;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____18888 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____18888
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____18899 =
                                        let uu____18904 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____18904  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____18899;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = [];
                                        FStar_Syntax_Syntax.lbpos =
                                          FStar_Range.dummyRange
                                      }  in
                                    let impl =
                                      let uu____18908 =
                                        let uu____18909 =
                                          let uu____18916 =
                                            let uu____18919 =
                                              let uu____18920 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____18920
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____18919]  in
                                          ((false, [lb]), uu____18916)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____18909
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____18908;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18762 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____18969,t,uu____18971,n1,uu____18973) when
            let uu____18980 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____18980 ->
            let uu____18982 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____18982 with
             | (formals,uu____19000) ->
                 (match formals with
                  | [] -> []
                  | uu____19029 ->
                      let filter_records uu___265_19045 =
                        match uu___265_19045 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19048,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19060 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19062 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19062 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____19074 = FStar_Util.first_N n1 formals  in
                      (match uu____19074 with
                       | (uu____19103,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19137 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun kopt  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____19216 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19216
                    then
                      let uu____19222 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19222
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19226 =
                      let uu____19231 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19231  in
                    let uu____19232 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19238 =
                          let uu____19241 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19241  in
                        FStar_Syntax_Util.arrow typars uu____19238
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19246 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19226;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19232;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19246;
                      FStar_Syntax_Syntax.lbattrs = [];
                      FStar_Syntax_Syntax.lbpos = rng
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
  
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___266_19300 =
            match uu___266_19300 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19302,uu____19303) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19313,uu____19314,uu____19315) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19325,uu____19326,uu____19327) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19357,uu____19358,uu____19359) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19405) ->
                let uu____19406 =
                  let uu____19407 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19407  in
                FStar_Parser_AST.mk_term uu____19406 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19409 =
                  let uu____19410 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19410  in
                FStar_Parser_AST.mk_term uu____19409 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19412) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____19443 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19451 =
                     let uu____19452 =
                       let uu____19459 = binder_to_term b  in
                       (out, uu____19459, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19452  in
                   FStar_Parser_AST.mk_term uu____19451
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___267_19471 =
            match uu___267_19471 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19528  ->
                       match uu____19528 with
                       | (x,t,uu____19539) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19545 =
                    let uu____19546 =
                      let uu____19547 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19547  in
                    FStar_Parser_AST.mk_term uu____19546
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19545 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19554 = binder_idents parms  in id1 ::
                    uu____19554
                   in
                (FStar_List.iter
                   (fun uu____19572  ->
                      match uu____19572 with
                      | (f,uu____19582,uu____19583) ->
                          let uu____19588 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19588
                          then
                            let uu____19593 =
                              let uu____19599 =
                                let uu____19601 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19601
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19599)
                               in
                            FStar_Errors.raise_error uu____19593
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19607 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19634  ->
                            match uu____19634 with
                            | (x,uu____19644,uu____19645) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19607)))
            | uu____19703 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___268_19743 =
            match uu___268_19743 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19767 = typars_of_binders _env binders  in
                (match uu____19767 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19803 =
                         let uu____19804 =
                           let uu____19805 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19805  in
                         FStar_Parser_AST.mk_term uu____19804
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19803 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____19816 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____19859 =
              FStar_List.fold_left
                (fun uu____19893  ->
                   fun uu____19894  ->
                     match (uu____19893, uu____19894) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____19963 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____19963 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____19859 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20054 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20054
                | uu____20055 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20063 = desugar_abstract_tc quals env [] tc  in
              (match uu____20063 with
               | (uu____20076,uu____20077,se,uu____20079) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20082,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20101 =
                                 let uu____20103 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20103  in
                               if uu____20101
                               then
                                 let uu____20106 =
                                   let uu____20112 =
                                     let uu____20114 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20114
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20112)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20106
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____20127 ->
                               let uu____20128 =
                                 let uu____20135 =
                                   let uu____20136 =
                                     let uu____20151 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20151)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20136
                                    in
                                 FStar_Syntax_Syntax.mk uu____20135  in
                               uu____20128 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___311_20167 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___311_20167.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___311_20167.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___311_20167.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20168 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20172 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20172
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20185 = typars_of_binders env binders  in
              (match uu____20185 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20219 =
                           FStar_Util.for_some
                             (fun uu___269_20222  ->
                                match uu___269_20222 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20225 -> false) quals
                            in
                         if uu____20219
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20233 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20233
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20238 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___270_20244  ->
                               match uu___270_20244 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20247 -> false))
                        in
                     if uu____20238
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20261 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20261
                     then
                       let uu____20267 =
                         let uu____20274 =
                           let uu____20275 = unparen t  in
                           uu____20275.FStar_Parser_AST.tm  in
                         match uu____20274 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20296 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20326)::args_rev ->
                                   let uu____20338 =
                                     let uu____20339 = unparen last_arg  in
                                     uu____20339.FStar_Parser_AST.tm  in
                                   (match uu____20338 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20367 -> ([], args))
                               | uu____20376 -> ([], args)  in
                             (match uu____20296 with
                              | (cattributes,args1) ->
                                  let uu____20415 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20415))
                         | uu____20426 -> (t, [])  in
                       match uu____20267 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___271_20449  ->
                                     match uu___271_20449 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20452 -> true))
                              in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars kopt1 t1 [qlid] quals1
                          rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____20461)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20485 = tycon_record_as_variant trec  in
              (match uu____20485 with
               | (t,fs) ->
                   let uu____20502 =
                     let uu____20505 =
                       let uu____20506 =
                         let uu____20515 =
                           let uu____20518 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20518  in
                         (uu____20515, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20506  in
                     uu____20505 :: quals  in
                   desugar_tycon env d uu____20502 [t])
          | uu____20523::uu____20524 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20694 = et  in
                match uu____20694 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20924 ->
                         let trec = tc  in
                         let uu____20948 = tycon_record_as_variant trec  in
                         (match uu____20948 with
                          | (t,fs) ->
                              let uu____21008 =
                                let uu____21011 =
                                  let uu____21012 =
                                    let uu____21021 =
                                      let uu____21024 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21024  in
                                    (uu____21021, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21012
                                   in
                                uu____21011 :: quals1  in
                              collect_tcs uu____21008 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21114 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21114 with
                          | (env2,uu____21175,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21328 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21328 with
                          | (env2,uu____21389,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21517 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21567 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21567 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___273_22082  ->
                             match uu___273_22082 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22148,uu____22149);
                                    FStar_Syntax_Syntax.sigrng = uu____22150;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22151;
                                    FStar_Syntax_Syntax.sigmeta = uu____22152;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22153;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22217 =
                                     typars_of_binders env1 binders  in
                                   match uu____22217 with
                                   | (env2,tpars1) ->
                                       let uu____22244 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22244 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____22273 =
                                   let uu____22292 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22292)
                                    in
                                 [uu____22273]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22352);
                                    FStar_Syntax_Syntax.sigrng = uu____22353;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22355;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22356;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____22457 = push_tparams env1 tpars
                                    in
                                 (match uu____22457 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22524  ->
                                             match uu____22524 with
                                             | (x,uu____22536) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22541 =
                                        let uu____22568 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22678  ->
                                                  match uu____22678 with
                                                  | (id1,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____22738 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22738
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___272_22749
                                                                 ->
                                                                match uu___272_22749
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22761
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22769 =
                                                        let uu____22788 =
                                                          let uu____22789 =
                                                            let uu____22790 =
                                                              let uu____22806
                                                                =
                                                                let uu____22807
                                                                  =
                                                                  let uu____22810
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22810
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22807
                                                                 in
                                                              (name, univs1,
                                                                uu____22806,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22790
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22789;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____22788)
                                                         in
                                                      (name, uu____22769)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22568
                                         in
                                      (match uu____22541 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 []
                                             })
                                           :: constrs1))
                             | uu____23026 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23154  ->
                             match uu____23154 with
                             | (name_doc,uu____23180,uu____23181) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23253  ->
                             match uu____23253 with
                             | (uu____23272,uu____23273,se) -> se))
                      in
                   let uu____23299 =
                     let uu____23306 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23306 rng
                      in
                   (match uu____23299 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____23368  ->
                                  match uu____23368 with
                                  | (uu____23389,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23437,tps,k,uu____23440,constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract
                                             quals1)
                                            &&
                                            (Prims.op_Negation
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Private
                                                  quals1))
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      let uu____23461 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23476 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23493,uu____23494,uu____23495,uu____23496,uu____23497)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23504
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23476
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23508 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___274_23515 
                                                          ->
                                                          match uu___274_23515
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23517 ->
                                                              true
                                                          | uu____23527 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23508))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23461
                                  | uu____23529 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23546  ->
                                 match uu____23546 with
                                 | (lid,doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____23591 =
        FStar_List.fold_left
          (fun uu____23626  ->
             fun b  ->
               match uu____23626 with
               | (env1,binders1) ->
                   let uu____23670 = desugar_binder env1 b  in
                   (match uu____23670 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23693 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23693 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23746 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23591 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____23850 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___275_23857  ->
                    match uu___275_23857 with
                    | FStar_Syntax_Syntax.Reflectable uu____23859 -> true
                    | uu____23861 -> false))
             in
          if uu____23850
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____23866 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____23866
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____23907 = FStar_Syntax_Util.head_and_args at1  in
      match uu____23907 with
      | (hd1,args) ->
          let uu____23960 =
            let uu____23975 =
              let uu____23976 = FStar_Syntax_Subst.compress hd1  in
              uu____23976.FStar_Syntax_Syntax.n  in
            (uu____23975, args)  in
          (match uu____23960 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24001)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24036 =
                 let uu____24041 =
                   let uu____24050 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24050 a1  in
                 uu____24041 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24036 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24080 =
                      let uu____24089 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24089, b)  in
                    FStar_Pervasives_Native.Some uu____24080
                | uu____24106 ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let b =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.fail_lax_attr
                  in
               FStar_Pervasives_Native.Some ([], b)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24160) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | uu____24195 -> FStar_Pervasives_Native.None)
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                    Prims.list))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                fun attrs  ->
                  let env0 = env  in
                  let monad_env =
                    FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                  let uu____24367 = desugar_binders monad_env eff_binders  in
                  match uu____24367 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let mandatory_members =
                        let rr_members =
                          ["repr";
                          "return";
                          "bind";
                          "wp_type";
                          "interp";
                          "mrelation"]  in
                        FStar_List.append rr_members
                          ["return_wp";
                          "bind_wp";
                          "if_then_else";
                          "ite_wp";
                          "stronger";
                          "close_wp";
                          "assert_p";
                          "assume_p";
                          "null_wp";
                          "trivial"]
                         in
                      let name_of_eff_decl decl =
                        match decl.FStar_Parser_AST.d with
                        | FStar_Parser_AST.Tycon
                            (uu____24456,uu____24457,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24459,uu____24460,uu____24461),uu____24462)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24499 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24502 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24514 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24514 mandatory_members)
                          eff_decls
                         in
                      (match uu____24502 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24533 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24562  ->
                                     fun decl  ->
                                       match uu____24562 with
                                       | (env2,out) ->
                                           let uu____24582 =
                                             desugar_decl env2 decl  in
                                           (match uu____24582 with
                                            | (env3,ses) ->
                                                let uu____24595 =
                                                  let uu____24598 =
                                                    FStar_List.hd ses  in
                                                  uu____24598 :: out  in
                                                (env3, uu____24595)))
                                  (env1, []))
                              in
                           (match uu____24533 with
                            | (env2,decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders
                                   in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1  ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____24661,uu____24662,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24665,defn),doc1)::[])
                                              ->
                                              let uu____24704 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24704 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24742 =
                                                     let uu____24743 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24744 =
                                                       let uu____24745 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24745
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24743;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24744;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24742, doc1))
                                          | uu____24754 ->
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                  "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                d1.FStar_Parser_AST.drange))
                                   in
                                let actions1 =
                                  FStar_List.map FStar_Pervasives_Native.fst
                                    actions_docs
                                   in
                                let eff_t1 =
                                  FStar_Syntax_Subst.close binders1 eff_t  in
                                let lookup_or_dummy s =
                                  let l =
                                    let uu____24792 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24792
                                     in
                                  let t =
                                    let uu____24797 =
                                      FStar_Syntax_DsEnv.try_lookup_definition
                                        env2 l
                                       in
                                    match uu____24797 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                    | FStar_Pervasives_Native.Some t ->
                                        FStar_Syntax_Subst.close binders1 t
                                     in
                                  ([], t)  in
                                let lookup_or_none s =
                                  let l =
                                    let uu____24824 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24824
                                     in
                                  let uu____24826 =
                                    FStar_Syntax_DsEnv.try_lookup_definition
                                      env2 l
                                     in
                                  match uu____24826 with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some t ->
                                      let uu____24844 =
                                        let uu____24851 =
                                          FStar_Syntax_Subst.close binders1 t
                                           in
                                        ([], uu____24851)  in
                                      FStar_Pervasives_Native.Some
                                        uu____24844
                                   in
                                let mname =
                                  FStar_Syntax_DsEnv.qualify env0 eff_name
                                   in
                                let qualifiers =
                                  FStar_List.map
                                    (trans_qual d.FStar_Parser_AST.drange
                                       (FStar_Pervasives_Native.Some mname))
                                    quals
                                   in
                                let se =
                                  let rr =
                                    FStar_Util.for_some
                                      (fun uu___276_24868  ->
                                         match uu___276_24868 with
                                         | FStar_Syntax_Syntax.Reifiable  ->
                                             true
                                         | FStar_Syntax_Syntax.Reflectable
                                             uu____24871 -> true
                                         | uu____24873 -> false) qualifiers
                                     in
                                  let uu____24875 =
                                    let uu____24876 =
                                      let uu____24877 =
                                        let uu____24878 =
                                          let uu____24879 =
                                            lookup_or_dummy "wp_type"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____24879
                                           in
                                        let uu____24901 =
                                          lookup_or_dummy "return_wp"  in
                                        let uu____24903 =
                                          lookup_or_dummy "bind_wp"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____24878;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____24901;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____24903
                                        }  in
                                      let uu____24905 =
                                        lookup_or_dummy "if_then_else"  in
                                      let uu____24907 =
                                        lookup_or_dummy "ite_wp"  in
                                      let uu____24909 =
                                        lookup_or_dummy "stronger"  in
                                      let uu____24911 =
                                        lookup_or_dummy "close_wp"  in
                                      let uu____24913 =
                                        lookup_or_dummy "assert_p"  in
                                      let uu____24915 =
                                        lookup_or_dummy "assume_p"  in
                                      let uu____24917 =
                                        lookup_or_dummy "null_wp"  in
                                      let uu____24919 =
                                        lookup_or_dummy "trivial"  in
                                      let uu____24921 =
                                        let uu____24922 =
                                          let uu____24923 =
                                            lookup_or_dummy "repr"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____24923
                                           in
                                        let uu____24939 =
                                          lookup_or_dummy "return"  in
                                        let uu____24941 =
                                          lookup_or_dummy "bind"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____24922;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____24939;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____24941
                                        }  in
                                      let uu____24943 =
                                        lookup_or_none "interp"  in
                                      let uu____24947 =
                                        lookup_or_none "mrelation"  in
                                      let uu____24951 =
                                        FStar_List.map (desugar_term env2)
                                          attrs
                                         in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.spec =
                                          uu____24877;
                                        FStar_Syntax_Syntax.signature =
                                          eff_t1;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____24905;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____24907;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____24909;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____24911;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____24913;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____24915;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____24917;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____24919;
                                        FStar_Syntax_Syntax.repr =
                                          uu____24921;
                                        FStar_Syntax_Syntax.elaborated =
                                          false;
                                        FStar_Syntax_Syntax.spec_dm4f = false;
                                        FStar_Syntax_Syntax.interp =
                                          uu____24943;
                                        FStar_Syntax_Syntax.mrelation =
                                          uu____24947;
                                        FStar_Syntax_Syntax.actions =
                                          actions1;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          uu____24951
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect
                                      uu____24876
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____24875;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }  in
                                let env3 =
                                  FStar_Syntax_DsEnv.push_sigelt env0 se  in
                                let env4 =
                                  FStar_Syntax_DsEnv.push_doc env3 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                let env5 =
                                  FStar_All.pipe_right actions_docs
                                    (FStar_List.fold_left
                                       (fun env5  ->
                                          fun uu____24979  ->
                                            match uu____24979 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____24993 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____24993
                                                   in
                                                FStar_Syntax_DsEnv.push_doc
                                                  env6
                                                  a.FStar_Syntax_Syntax.action_name
                                                  doc1) env4)
                                   in
                                let env6 =
                                  push_reflect_effect env5 qualifiers mname
                                    d.FStar_Parser_AST.drange
                                   in
                                let env7 =
                                  FStar_Syntax_DsEnv.push_doc env6 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                (env7, [se])))

and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____25017 = desugar_binders env1 eff_binders  in
                match uu____25017 with
                | (env2,binders) ->
                    let uu____25054 =
                      let uu____25065 = head_and_args defn  in
                      match uu____25065 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25102 ->
                                let uu____25103 =
                                  let uu____25109 =
                                    let uu____25111 =
                                      let uu____25113 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____25113 " not found"
                                       in
                                    Prims.strcat "Effect " uu____25111  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25109)
                                   in
                                FStar_Errors.raise_error uu____25103
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25119 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25149)::args_rev ->
                                let uu____25161 =
                                  let uu____25162 = unparen last_arg  in
                                  uu____25162.FStar_Parser_AST.tm  in
                                (match uu____25161 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25190 -> ([], args))
                            | uu____25199 -> ([], args)  in
                          (match uu____25119 with
                           | (cattributes,args1) ->
                               let uu____25242 = desugar_args env2 args1  in
                               let uu____25243 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25242, uu____25243))
                       in
                    (match uu____25054 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____25283 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25283 with
                           | (ed_binders,uu____25297,ed_binders_opening) ->
                               let sub' shift_n uu____25316 =
                                 match uu____25316 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25331 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25331 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25335 =
                                       let uu____25336 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25336)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25335
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25357 =
                                   let uu____25358 =
                                     let uu____25359 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25359
                                      in
                                   let uu____25374 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25375 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25358;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25374;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25375
                                   }  in
                                 let uu____25376 =
                                   let uu____25377 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25377
                                    in
                                 let uu____25392 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25393 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25394 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25395 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25396 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25397 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25398 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25399 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25400 =
                                   let uu____25401 =
                                     let uu____25402 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25402
                                      in
                                   let uu____25417 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25418 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25401;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25417;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25418
                                   }  in
                                 let uu____25419 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.interp sub1
                                    in
                                 let uu____25422 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.mrelation sub1
                                    in
                                 let uu____25425 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25441 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25442 =
                                          let uu____25443 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25443
                                           in
                                        let uu____25464 =
                                          let uu____25465 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25465
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25441;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25442;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25464
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.spec = uu____25357;
                                   FStar_Syntax_Syntax.signature =
                                     uu____25376;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25392;
                                   FStar_Syntax_Syntax.ite_wp = uu____25393;
                                   FStar_Syntax_Syntax.stronger = uu____25394;
                                   FStar_Syntax_Syntax.close_wp = uu____25395;
                                   FStar_Syntax_Syntax.assert_p = uu____25396;
                                   FStar_Syntax_Syntax.assume_p = uu____25397;
                                   FStar_Syntax_Syntax.null_wp = uu____25398;
                                   FStar_Syntax_Syntax.trivial = uu____25399;
                                   FStar_Syntax_Syntax.repr = uu____25400;
                                   FStar_Syntax_Syntax.elaborated =
                                     (ed.FStar_Syntax_Syntax.elaborated);
                                   FStar_Syntax_Syntax.spec_dm4f =
                                     (ed.FStar_Syntax_Syntax.spec_dm4f);
                                   FStar_Syntax_Syntax.interp = uu____25419;
                                   FStar_Syntax_Syntax.mrelation =
                                     uu____25422;
                                   FStar_Syntax_Syntax.actions = uu____25425;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____25487 =
                                   let uu____25490 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25490 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____25487;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____25511 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25511
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25513 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25513
                                 then
                                   let reflect_lid =
                                     let uu____25520 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25520
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____25532 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25532 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25617 ->
              let uu____25620 =
                let uu____25622 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25622
                 in
              Prims.strcat "\n  " uu____25620
          | uu____25625 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25644  ->
               match uu____25644 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text))
           in
        let fv =
          let uu____25689 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25689
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25692 =
          let uu____25703 = FStar_Syntax_Syntax.as_arg arg  in [uu____25703]
           in
        FStar_Syntax_Util.mk_app fv uu____25692

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25734 = desugar_decl_noattrs env d  in
      match uu____25734 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25752 = mk_comment_attr d  in uu____25752 :: attrs1  in
          let uu____25753 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___312_25763 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___312_25763.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___312_25763.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___312_25763.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___312_25763.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___313_25766 = sigelt  in
                      let uu____25767 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____25773 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____25773) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___313_25766.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___313_25766.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___313_25766.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___313_25766.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25767
                      })) sigelts
             in
          (env1, uu____25753)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25799 = desugar_decl_aux env d  in
      match uu____25799 with
      | (env1,ses) ->
          let uu____25810 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____25810)

and (desugar_decl_noattrs :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let p1 = trans_pragma p  in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            (env, [se])))
      | FStar_Parser_AST.Fsdoc uu____25838 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____25843 = FStar_Syntax_DsEnv.iface env  in
          if uu____25843
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____25858 =
               let uu____25860 =
                 let uu____25862 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____25863 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____25862
                   uu____25863
                  in
               Prims.op_Negation uu____25860  in
             if uu____25858
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____25877 =
                  let uu____25879 =
                    let uu____25881 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____25881 lid  in
                  Prims.op_Negation uu____25879  in
                if uu____25877
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____25895 =
                     let uu____25897 =
                       let uu____25899 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____25899
                         lid
                        in
                     Prims.op_Negation uu____25897  in
                   if uu____25895
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____25917 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____25917, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____25958,uu____25959)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____25998 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26025  ->
                 match uu____26025 with | (x,uu____26033) -> x) tcs
             in
          let uu____26038 =
            let uu____26043 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26043 tcs1  in
          (match uu____26038 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26060 =
                   let uu____26061 =
                     let uu____26068 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26068  in
                   [uu____26061]  in
                 let uu____26081 =
                   let uu____26084 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26087 =
                     let uu____26098 =
                       let uu____26107 =
                         let uu____26108 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26108  in
                       FStar_Syntax_Syntax.as_arg uu____26107  in
                     [uu____26098]  in
                   FStar_Syntax_Util.mk_app uu____26084 uu____26087  in
                 FStar_Syntax_Util.abs uu____26060 uu____26081
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26148,id1))::uu____26150 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26153::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26157 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26157 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26163 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26163]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26184) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26194,uu____26195,uu____26196,uu____26197,uu____26198)
                     ->
                     let uu____26207 =
                       let uu____26208 =
                         let uu____26209 =
                           let uu____26216 = mkclass lid  in
                           (meths, uu____26216)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26209  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26208;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26207]
                 | uu____26219 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26253;
                    FStar_Parser_AST.prange = uu____26254;_},uu____26255)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26265;
                    FStar_Parser_AST.prange = uu____26266;_},uu____26267)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26283;
                         FStar_Parser_AST.prange = uu____26284;_},uu____26285);
                    FStar_Parser_AST.prange = uu____26286;_},uu____26287)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26309;
                         FStar_Parser_AST.prange = uu____26310;_},uu____26311);
                    FStar_Parser_AST.prange = uu____26312;_},uu____26313)::[]
                   -> false
               | (p,uu____26342)::[] ->
                   let uu____26351 = is_app_pattern p  in
                   Prims.op_Negation uu____26351
               | uu____26353 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let uu____26428 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26428 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26441 =
                     let uu____26442 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26442.FStar_Syntax_Syntax.n  in
                   match uu____26441 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26452) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let quals1 =
                         match quals with
                         | uu____26488::uu____26489 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26492 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___277_26508  ->
                                     match uu___277_26508 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26511;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26512;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26513;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26514;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26515;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26516;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26517;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26529;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26530;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26531;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26532;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26533;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26534;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26548 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26581  ->
                                   match uu____26581 with
                                   | (uu____26595,(uu____26596,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26548
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26616 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26616
                         then
                           let uu____26622 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___314_26637 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___315_26639 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___315_26639.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___315_26639.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___314_26637.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26622)
                         else lbs  in
                       let names1 =
                         FStar_All.pipe_right fvs
                           (FStar_List.map
                              (fun fv  ->
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let attrs =
                         FStar_List.map (desugar_term env)
                           d.FStar_Parser_AST.attrs
                          in
                       let s =
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                           FStar_Syntax_Syntax.sigrng =
                             (d.FStar_Parser_AST.drange);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = attrs
                         }  in
                       let env1 = FStar_Syntax_DsEnv.push_sigelt env s  in
                       let env2 =
                         FStar_List.fold_left
                           (fun env2  ->
                              fun id1  ->
                                FStar_Syntax_DsEnv.push_doc env2 id1
                                  d.FStar_Parser_AST.doc) env1 names1
                          in
                       (env2, [s])
                   | uu____26669 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26677 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26696 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26677 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___316_26733 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___316_26733.FStar_Parser_AST.prange)
                       }
                   | uu____26740 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___317_26747 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___317_26747.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___317_26747.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___317_26747.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____26783 id1 =
                   match uu____26783 with
                   | (env1,ses) ->
                       let main =
                         let uu____26804 =
                           let uu____26805 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____26805  in
                         FStar_Parser_AST.mk_term uu____26804
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____26855 = desugar_decl env1 id_decl  in
                       (match uu____26855 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____26873 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____26873 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____26897 = close_fun env t  in
            desugar_term env uu____26897  in
          let quals1 =
            let uu____26901 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____26901
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____26910 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____26910;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____26924 =
                  let uu____26933 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____26933]  in
                let uu____26952 =
                  let uu____26955 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____26955
                   in
                FStar_Syntax_Util.arrow uu____26924 uu____26952
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
            attrs
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____27010 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27010 with
            | FStar_Pervasives_Native.None  ->
                let uu____27013 =
                  let uu____27019 =
                    let uu____27021 =
                      let uu____27023 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____27023 " not found"  in
                    Prims.strcat "Effect name " uu____27021  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27019)  in
                FStar_Errors.raise_error uu____27013
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27031 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27049 =
                  let uu____27052 =
                    let uu____27053 = desugar_term env t  in
                    ([], uu____27053)  in
                  FStar_Pervasives_Native.Some uu____27052  in
                (uu____27049, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27066 =
                  let uu____27069 =
                    let uu____27070 = desugar_term env wp  in
                    ([], uu____27070)  in
                  FStar_Pervasives_Native.Some uu____27069  in
                let uu____27077 =
                  let uu____27080 =
                    let uu____27081 = desugar_term env t  in
                    ([], uu____27081)  in
                  FStar_Pervasives_Native.Some uu____27080  in
                (uu____27066, uu____27077)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27093 =
                  let uu____27096 =
                    let uu____27097 = desugar_term env t  in
                    ([], uu____27097)  in
                  FStar_Pervasives_Native.Some uu____27096  in
                (FStar_Pervasives_Native.None, uu____27093)
             in
          (match uu____27031 with
           | (lift_wp,lift) ->
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect
                        {
                          FStar_Syntax_Syntax.source = src;
                          FStar_Syntax_Syntax.target = dst;
                          FStar_Syntax_Syntax.lift_wp = lift_wp;
                          FStar_Syntax_Syntax.lift = lift
                        });
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               (env, [se]))
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27131 =
              let uu____27132 =
                let uu____27139 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27139, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27132  in
            {
              FStar_Syntax_Syntax.sigel = uu____27131;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27166 =
        FStar_List.fold_left
          (fun uu____27186  ->
             fun d  ->
               match uu____27186 with
               | (env1,sigelts) ->
                   let uu____27206 = desugar_decl env1 d  in
                   (match uu____27206 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27166 with
      | (env1,sigelts) ->
          let rec forward acc uu___279_27251 =
            match uu___279_27251 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27265,FStar_Syntax_Syntax.Sig_let uu____27266) ->
                     let uu____27279 =
                       let uu____27282 =
                         let uu___318_27283 = se2  in
                         let uu____27284 =
                           let uu____27287 =
                             FStar_List.filter
                               (fun uu___278_27301  ->
                                  match uu___278_27301 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27306;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27307;_},uu____27308);
                                      FStar_Syntax_Syntax.pos = uu____27309;
                                      FStar_Syntax_Syntax.vars = uu____27310;_}
                                      when
                                      let uu____27337 =
                                        let uu____27339 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27339
                                         in
                                      uu____27337 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27343 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27287
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___318_27283.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___318_27283.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___318_27283.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___318_27283.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27284
                         }  in
                       uu____27282 :: se1 :: acc  in
                     forward uu____27279 sigelts1
                 | uu____27349 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27357 = forward [] sigelts  in (env1, uu____27357)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____27422) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27426;
               FStar_Syntax_Syntax.exports = uu____27427;
               FStar_Syntax_Syntax.is_interface = uu____27428;_},FStar_Parser_AST.Module
             (current_lid,uu____27430)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27439) ->
              let uu____27442 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27442
           in
        let uu____27447 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27489 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27489, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27511 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27511, mname, decls, false)
           in
        match uu____27447 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27553 = desugar_decls env2 decls  in
            (match uu____27553 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____27621 =
            (FStar_Options.interactive ()) &&
              (let uu____27624 =
                 let uu____27626 =
                   let uu____27628 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27628  in
                 FStar_Util.get_file_extension uu____27626  in
               FStar_List.mem uu____27624 ["fsti"; "fsi"])
             in
          if uu____27621 then as_interface m else m  in
        let uu____27642 = desugar_modul_common curmod env m1  in
        match uu____27642 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27664 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27664, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27686 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27686 with
      | (env1,modul,pop_when_done) ->
          let uu____27703 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27703 with
           | (env2,modul1) ->
               ((let uu____27715 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27715
                 then
                   let uu____27718 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27718
                 else ());
                (let uu____27723 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27723, modul1))))
  
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    FStar_Options.push ();
    (let res = f ()  in
     let light = FStar_Options.ml_ish ()  in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      with_options
        (fun uu____27777  ->
           let uu____27778 = desugar_modul env modul  in
           match uu____27778 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____27820  ->
           let uu____27821 = desugar_decls env decls  in
           match uu____27821 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____27876  ->
             let uu____27877 = desugar_partial_modul modul env a_modul  in
             match uu____27877 with | (env1,modul1) -> (modul1, env1))
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____27976 ->
                  let t =
                    let uu____27986 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____27986  in
                  let uu____27999 =
                    let uu____28000 = FStar_Syntax_Subst.compress t  in
                    uu____28000.FStar_Syntax_Syntax.n  in
                  (match uu____27999 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28012,uu____28013)
                       -> bs1
                   | uu____28038 -> failwith "Impossible")
               in
            let uu____28048 =
              let uu____28055 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28055
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28048 with
            | (binders,uu____28057,binders_opening) ->
                let erase_term t =
                  let uu____28065 =
                    let uu____28066 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28066  in
                  FStar_Syntax_Subst.close binders uu____28065  in
                let erase_tscheme uu____28084 =
                  match uu____28084 with
                  | (us,t) ->
                      let t1 =
                        let uu____28104 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28104 t  in
                      let uu____28107 =
                        let uu____28108 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28108  in
                      ([], uu____28107)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____28131 ->
                        let bs =
                          let uu____28141 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28141  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28181 =
                          let uu____28182 =
                            let uu____28185 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28185  in
                          uu____28182.FStar_Syntax_Syntax.n  in
                        (match uu____28181 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28187,uu____28188) -> bs1
                         | uu____28213 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28221 =
                      let uu____28222 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28222  in
                    FStar_Syntax_Subst.close binders uu____28221  in
                  let uu___319_28223 = action  in
                  let uu____28224 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28225 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___319_28223.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___319_28223.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28224;
                    FStar_Syntax_Syntax.action_typ = uu____28225
                  }  in
                let uu___320_28226 = ed  in
                let uu____28227 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28228 =
                  let uu____28229 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28230 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28231 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28229;
                    FStar_Syntax_Syntax.monad_ret = uu____28230;
                    FStar_Syntax_Syntax.monad_bind = uu____28231
                  }  in
                let uu____28232 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28233 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28234 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28235 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28236 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28237 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28238 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28239 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28240 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28241 =
                  let uu____28242 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28243 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28244 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28242;
                    FStar_Syntax_Syntax.monad_ret = uu____28243;
                    FStar_Syntax_Syntax.monad_bind = uu____28244
                  }  in
                let uu____28245 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___320_28226.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___320_28226.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28227;
                  FStar_Syntax_Syntax.spec = uu____28228;
                  FStar_Syntax_Syntax.signature = uu____28232;
                  FStar_Syntax_Syntax.if_then_else = uu____28233;
                  FStar_Syntax_Syntax.ite_wp = uu____28234;
                  FStar_Syntax_Syntax.stronger = uu____28235;
                  FStar_Syntax_Syntax.close_wp = uu____28236;
                  FStar_Syntax_Syntax.assert_p = uu____28237;
                  FStar_Syntax_Syntax.assume_p = uu____28238;
                  FStar_Syntax_Syntax.null_wp = uu____28239;
                  FStar_Syntax_Syntax.trivial = uu____28240;
                  FStar_Syntax_Syntax.repr = uu____28241;
                  FStar_Syntax_Syntax.elaborated =
                    (uu___320_28226.FStar_Syntax_Syntax.elaborated);
                  FStar_Syntax_Syntax.spec_dm4f =
                    (uu___320_28226.FStar_Syntax_Syntax.spec_dm4f);
                  FStar_Syntax_Syntax.interp =
                    (uu___320_28226.FStar_Syntax_Syntax.interp);
                  FStar_Syntax_Syntax.mrelation =
                    (uu___320_28226.FStar_Syntax_Syntax.mrelation);
                  FStar_Syntax_Syntax.actions = uu____28245;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___320_28226.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___321_28261 = se  in
                  let uu____28262 =
                    let uu____28263 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28263  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28262;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___321_28261.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___321_28261.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___321_28261.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___321_28261.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28265 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28266 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28266 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28283 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28283
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28285 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28285)
  