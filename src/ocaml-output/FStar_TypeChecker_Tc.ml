open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst in
      let get_n lid =
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else (Prims.parse_int "0") in
      let uu____48 = FStar_Options.reuse_hint_for () in
      match uu____48 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____53 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____53 l in
          let uu___68_54 = env in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid in (lid, uu____80) in
              FStar_Pervasives_Native.Some uu____75 in
            (tbl, uu____68) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___68_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___68_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___68_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___68_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___68_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___68_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___68_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___68_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___68_54.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___68_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___68_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___68_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___68_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___68_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___68_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___68_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___68_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___68_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___68_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___68_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___68_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___68_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___68_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___68_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___68_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___68_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___68_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___68_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___68_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___68_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___68_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___68_54.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___68_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___68_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___68_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___68_54.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____97 = FStar_TypeChecker_Env.current_module env in
                let uu____98 =
                  let uu____99 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____99 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____97 uu____98
            | l::uu____101 -> l in
          let uu___69_104 = env in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid in (lid, uu____130) in
              FStar_Pervasives_Native.Some uu____125 in
            (tbl, uu____118) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___69_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___69_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___69_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___69_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___69_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___69_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___69_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___69_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___69_104.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___69_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___69_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___69_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___69_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___69_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___69_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___69_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___69_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___69_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___69_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___69_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___69_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___69_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___69_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___69_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___69_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___69_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___69_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___69_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___69_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___69_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___69_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___69_104.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___69_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___69_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___69_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___69_104.FStar_TypeChecker_Env.dep_graph)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu____149 =
         let uu____150 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____150 in
       Prims.op_Negation uu____149)
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____166 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____166 with
        | (t1, c, g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun env ->
      fun t ->
        (let uu____193 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____193
         then
           let uu____194 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____194
         else ());
        (let uu____196 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____196 with
         | (t', uu____204, uu____205) ->
             ((let uu____207 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____207
               then
                 let uu____208 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____208
               else ());
              t'))
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun t ->
      fun k ->
        let uu____225 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____225
let check_nogen :
  'Auu____234 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____234 Prims.list, FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun t ->
      fun k ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____257 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____257)
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun m ->
      fun s ->
        let fail1 uu____292 =
          let uu____293 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____298 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____293 uu____298 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____338)::(wp, uu____340)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____355 -> fail1 ())
        | uu____356 -> fail1 ()
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      let uu____367 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____367 with
      | (open_annotated_univs, annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____397 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____397 t in
          let open_univs_binders n_binders bs =
            let uu____411 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____411 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____419 =
            let uu____426 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders in
            let uu____427 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____426 uu____427 in
          (match uu____419 with
           | (effect_params_un, signature_un, opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names in
               let uu____438 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un in
               (match uu____438 with
                | (effect_params, env1, uu____447) ->
                    let uu____448 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un in
                    (match uu____448 with
                     | (signature, uu____454) ->
                         let ed1 =
                           let uu___70_456 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___70_456.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___70_456.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___70_456.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___70_456.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___70_456.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___70_456.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___70_456.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___70_456.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___70_456.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___70_456.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___70_456.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___70_456.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___70_456.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___70_456.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___70_456.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___70_456.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___70_456.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___70_456.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([], []) -> ed1
                           | uu____472 ->
                               let op uu____496 =
                                 match uu____496 with
                                 | (us, t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____516 =
                                       let uu____517 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____526 = open_univs n_us t in
                                       FStar_Syntax_Subst.subst uu____517
                                         uu____526 in
                                     (us, uu____516) in
                               let uu___71_535 = ed1 in
                               let uu____536 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____537 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____538 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____539 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____540 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____541 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____542 =
                                 op ed1.FStar_Syntax_Syntax.assert_p in
                               let uu____543 =
                                 op ed1.FStar_Syntax_Syntax.assume_p in
                               let uu____544 =
                                 op ed1.FStar_Syntax_Syntax.null_wp in
                               let uu____545 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____546 =
                                 let uu____547 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____547 in
                               let uu____558 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____559 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____560 =
                                 FStar_List.map
                                   (fun a ->
                                      let uu___72_568 = a in
                                      let uu____569 =
                                        let uu____570 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____570 in
                                      let uu____579 =
                                        let uu____580 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd uu____580 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___72_568.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___72_568.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___72_568.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___72_568.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____569;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____579
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___71_535.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___71_535.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___71_535.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___71_535.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____536;
                                 FStar_Syntax_Syntax.bind_wp = uu____537;
                                 FStar_Syntax_Syntax.if_then_else = uu____538;
                                 FStar_Syntax_Syntax.ite_wp = uu____539;
                                 FStar_Syntax_Syntax.stronger = uu____540;
                                 FStar_Syntax_Syntax.close_wp = uu____541;
                                 FStar_Syntax_Syntax.assert_p = uu____542;
                                 FStar_Syntax_Syntax.assume_p = uu____543;
                                 FStar_Syntax_Syntax.null_wp = uu____544;
                                 FStar_Syntax_Syntax.trivial = uu____545;
                                 FStar_Syntax_Syntax.repr = uu____546;
                                 FStar_Syntax_Syntax.return_repr = uu____558;
                                 FStar_Syntax_Syntax.bind_repr = uu____559;
                                 FStar_Syntax_Syntax.actions = uu____560;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___71_535.FStar_Syntax_Syntax.eff_attrs)
                               } in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____623 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t in
                             let uu____628 = FStar_Ident.range_of_lid mname in
                             FStar_Errors.raise_error uu____623 uu____628 in
                           let uu____635 =
                             let uu____636 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____636.FStar_Syntax_Syntax.n in
                           match uu____635 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a, uu____671)::(wp, uu____673)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____688 -> fail1 signature1)
                           | uu____689 -> fail1 signature1 in
                         let uu____690 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____690 with
                          | (a, wp_a) ->
                              let fresh_effect_signature uu____714 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____721 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un in
                                    (match uu____721 with
                                     | (signature1, uu____733) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____734 ->
                                    let uu____737 =
                                      let uu____742 =
                                        let uu____743 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____743) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____742 in
                                    (match uu____737 with
                                     | (uu____752, signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env2 =
                                let uu____755 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env1 uu____755 in
                              ((let uu____757 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____757
                                then
                                  let uu____758 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____759 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____760 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____761 =
                                    let uu____762 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____762 in
                                  let uu____763 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____758 uu____759 uu____760 uu____761
                                    uu____763
                                else ());
                               (let check_and_gen' env3 uu____785 k =
                                  match uu____785 with
                                  | (us, t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____799::uu____800 ->
                                           let uu____803 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____803 with
                                            | (us1, t1) ->
                                                let uu____812 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____812 with
                                                 | (us2, t2) ->
                                                     let uu____819 =
                                                       let uu____820 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2 in
                                                       tc_check_trivial_guard
                                                         uu____820 t2 k in
                                                     let uu____821 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____821)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____826 =
                                      let uu____833 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____834 =
                                        let uu____837 =
                                          let uu____838 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____838 in
                                        [uu____837] in
                                      uu____833 :: uu____834 in
                                    let uu____839 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____826
                                      uu____839 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____843 = fresh_effect_signature () in
                                  match uu____843 with
                                  | (b, wp_b) ->
                                      let a_wp_b =
                                        let uu____859 =
                                          let uu____866 =
                                            let uu____867 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____867 in
                                          [uu____866] in
                                        let uu____868 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____859
                                          uu____868 in
                                      let expected_k =
                                        let uu____874 =
                                          let uu____881 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____882 =
                                            let uu____885 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____886 =
                                              let uu____889 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____890 =
                                                let uu____893 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____894 =
                                                  let uu____897 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____897] in
                                                uu____893 :: uu____894 in
                                              uu____889 :: uu____890 in
                                            uu____885 :: uu____886 in
                                          uu____881 :: uu____882 in
                                        let uu____898 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____874
                                          uu____898 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____903 =
                                      let uu____906 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname in
                                      FStar_Pervasives_Native.Some uu____906 in
                                    FStar_Syntax_Syntax.new_bv uu____903
                                      FStar_Syntax_Util.kprop in
                                  let expected_k =
                                    let uu____910 =
                                      let uu____917 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____918 =
                                        let uu____921 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____922 =
                                          let uu____925 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____926 =
                                            let uu____929 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____929] in
                                          uu____925 :: uu____926 in
                                        uu____921 :: uu____922 in
                                      uu____917 :: uu____918 in
                                    let uu____930 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____910
                                      uu____930 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____937 =
                                      let uu____944 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____945 =
                                        let uu____948 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____948] in
                                      uu____944 :: uu____945 in
                                    let uu____949 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____937
                                      uu____949 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____953 = FStar_Syntax_Util.type_u () in
                                  match uu____953 with
                                  | (t, uu____959) ->
                                      let expected_k =
                                        let uu____963 =
                                          let uu____970 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____971 =
                                            let uu____974 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____975 =
                                              let uu____978 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____978] in
                                            uu____974 :: uu____975 in
                                          uu____970 :: uu____971 in
                                        let uu____979 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____963
                                          uu____979 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____984 =
                                      let uu____987 =
                                        FStar_Ident.range_of_lid
                                          ed2.FStar_Syntax_Syntax.mname in
                                      FStar_Pervasives_Native.Some uu____987 in
                                    let uu____988 =
                                      let uu____989 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____989
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv uu____984
                                      uu____988 in
                                  let b_wp_a =
                                    let uu____1001 =
                                      let uu____1008 =
                                        let uu____1009 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1009 in
                                      [uu____1008] in
                                    let uu____1010 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1001
                                      uu____1010 in
                                  let expected_k =
                                    let uu____1016 =
                                      let uu____1023 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1024 =
                                        let uu____1027 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____1028 =
                                          let uu____1031 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____1031] in
                                        uu____1027 :: uu____1028 in
                                      uu____1023 :: uu____1024 in
                                    let uu____1032 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1016
                                      uu____1032 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let assert_p =
                                  let expected_k =
                                    let uu____1039 =
                                      let uu____1046 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1047 =
                                        let uu____1050 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Util.kprop in
                                        let uu____1051 =
                                          let uu____1054 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1054] in
                                        uu____1050 :: uu____1051 in
                                      uu____1046 :: uu____1047 in
                                    let uu____1055 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1039
                                      uu____1055 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k in
                                let assume_p =
                                  let expected_k =
                                    let uu____1062 =
                                      let uu____1069 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1070 =
                                        let uu____1073 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Util.kprop in
                                        let uu____1074 =
                                          let uu____1077 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1077] in
                                        uu____1073 :: uu____1074 in
                                      uu____1069 :: uu____1070 in
                                    let uu____1078 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1062
                                      uu____1078 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k in
                                let null_wp =
                                  let expected_k =
                                    let uu____1085 =
                                      let uu____1092 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      [uu____1092] in
                                    let uu____1093 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1085
                                      uu____1093 in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1097 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1097 with
                                  | (t, uu____1103) ->
                                      let expected_k =
                                        let uu____1107 =
                                          let uu____1114 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1115 =
                                            let uu____1118 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1118] in
                                          uu____1114 :: uu____1115 in
                                        let uu____1119 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1107
                                          uu____1119 in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1122 =
                                  let uu____1133 =
                                    let uu____1134 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1134.FStar_Syntax_Syntax.n in
                                  match uu____1133 with
                                  | FStar_Syntax_Syntax.Tm_unknown ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1149 ->
                                      let repr =
                                        let uu____1151 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1151 with
                                        | (t, uu____1157) ->
                                            let expected_k =
                                              let uu____1161 =
                                                let uu____1168 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1169 =
                                                  let uu____1172 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1172] in
                                                uu____1168 :: uu____1169 in
                                              let uu____1173 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1161 uu____1173 in
                                            tc_check_trivial_guard env2
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env2 repr in
                                        let uu____1190 =
                                          let uu____1197 =
                                            let uu____1198 =
                                              let uu____1213 =
                                                let uu____1216 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1217 =
                                                  let uu____1220 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1220] in
                                                uu____1216 :: uu____1217 in
                                              (repr1, uu____1213) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1198 in
                                          FStar_Syntax_Syntax.mk uu____1197 in
                                        uu____1190
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1239 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1239 wp in
                                      let destruct_repr t =
                                        let uu____1254 =
                                          let uu____1255 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1255.FStar_Syntax_Syntax.n in
                                        match uu____1254 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1266,
                                             (t1, uu____1268)::(wp,
                                                                uu____1270)::[])
                                            -> (t1, wp)
                                        | uu____1313 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____1324 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____1324
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____1325 =
                                          fresh_effect_signature () in
                                        match uu____1325 with
                                        | (b, wp_b) ->
                                            let a_wp_b =
                                              let uu____1341 =
                                                let uu____1348 =
                                                  let uu____1349 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1349 in
                                                [uu____1348] in
                                              let uu____1350 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____1341 uu____1350 in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b in
                                            let x_a =
                                              let uu____1356 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1356 in
                                            let wp_g_x =
                                              let uu____1360 =
                                                let uu____1365 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____1366 =
                                                  let uu____1367 =
                                                    let uu____1368 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1368 in
                                                  [uu____1367] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1365 uu____1366 in
                                              uu____1360
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____1377 =
                                                  let uu____1382 =
                                                    let uu____1383 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____1383
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____1392 =
                                                    let uu____1393 =
                                                      let uu____1396 =
                                                        let uu____1399 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____1400 =
                                                          let uu____1403 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____1404 =
                                                            let uu____1407 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____1408 =
                                                              let uu____1411
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____1411] in
                                                            uu____1407 ::
                                                              uu____1408 in
                                                          uu____1403 ::
                                                            uu____1404 in
                                                        uu____1399 ::
                                                          uu____1400 in
                                                      r :: uu____1396 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1393 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1382 uu____1392 in
                                                uu____1377
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let maybe_range_arg =
                                              let uu____1417 =
                                                FStar_Util.for_some
                                                  (FStar_Syntax_Util.attr_eq
                                                     FStar_Syntax_Util.dm4f_bind_range_attr)
                                                  ed2.FStar_Syntax_Syntax.eff_attrs in
                                              if uu____1417
                                              then
                                                let uu____1420 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    FStar_Syntax_Syntax.t_range in
                                                let uu____1421 =
                                                  let uu____1424 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range in
                                                  [uu____1424] in
                                                uu____1420 :: uu____1421
                                              else [] in
                                            let expected_k =
                                              let uu____1429 =
                                                let uu____1436 =
                                                  let uu____1439 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____1440 =
                                                    let uu____1443 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        b in
                                                    [uu____1443] in
                                                  uu____1439 :: uu____1440 in
                                                let uu____1444 =
                                                  let uu____1447 =
                                                    let uu____1450 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____1451 =
                                                      let uu____1454 =
                                                        let uu____1455 =
                                                          let uu____1456 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____1456 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1455 in
                                                      let uu____1457 =
                                                        let uu____1460 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____1461 =
                                                          let uu____1464 =
                                                            let uu____1465 =
                                                              let uu____1466
                                                                =
                                                                let uu____1473
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____1473] in
                                                              let uu____1474
                                                                =
                                                                let uu____1477
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1477 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1466
                                                                uu____1474 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1465 in
                                                          [uu____1464] in
                                                        uu____1460 ::
                                                          uu____1461 in
                                                      uu____1454 ::
                                                        uu____1457 in
                                                    uu____1450 :: uu____1451 in
                                                  FStar_List.append
                                                    maybe_range_arg
                                                    uu____1447 in
                                                FStar_List.append uu____1436
                                                  uu____1444 in
                                              let uu____1478 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____1429 uu____1478 in
                                            let uu____1481 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k in
                                            (match uu____1481 with
                                             | (expected_k1, uu____1489,
                                                uu____1490) ->
                                                 let env3 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env2
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env4 =
                                                   let uu___73_1495 = env3 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                     FStar_TypeChecker_Env.normalized_eff_names
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.normalized_eff_names);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth_hook
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.synth_hook);
                                                     FStar_TypeChecker_Env.splice
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.splice);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___73_1495.FStar_TypeChecker_Env.dep_graph)
                                                   } in
                                                 let br =
                                                   check_and_gen' env4
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____1505 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1505 in
                                        let res =
                                          let wp =
                                            let uu____1512 =
                                              let uu____1517 =
                                                let uu____1518 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____1518
                                                  FStar_Pervasives_Native.snd in
                                              let uu____1527 =
                                                let uu____1528 =
                                                  let uu____1531 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____1532 =
                                                    let uu____1535 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____1535] in
                                                  uu____1531 :: uu____1532 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1528 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1517 uu____1527 in
                                            uu____1512
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____1541 =
                                            let uu____1548 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1549 =
                                              let uu____1552 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____1552] in
                                            uu____1548 :: uu____1549 in
                                          let uu____1553 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____1541
                                            uu____1553 in
                                        let uu____1556 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env2 expected_k in
                                        match uu____1556 with
                                        | (expected_k1, uu____1570,
                                           uu____1571) ->
                                            let env3 =
                                              FStar_TypeChecker_Env.set_range
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____1575 =
                                              check_and_gen' env3
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____1575 with
                                             | (univs1, repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1596 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos)) in
                                      let actions =
                                        let check_action act =
                                          let uu____1615 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env2, act)
                                            else
                                              (let uu____1625 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs in
                                               match uu____1625 with
                                               | (usubst, uvs) ->
                                                   let uu____1648 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env2 uvs in
                                                   let uu____1649 =
                                                     let uu___74_1650 = act in
                                                     let uu____1651 =
                                                       FStar_Syntax_Subst.subst_binders
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_params in
                                                     let uu____1652 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn in
                                                     let uu____1653 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___74_1650.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___74_1650.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         = uu____1651;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____1652;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____1653
                                                     } in
                                                   (uu____1648, uu____1649)) in
                                          match uu____1615 with
                                          | (env3, act1) ->
                                              let act_typ =
                                                let uu____1659 =
                                                  let uu____1660 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ in
                                                  uu____1660.FStar_Syntax_Syntax.n in
                                                match uu____1659 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs, c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c in
                                                    let uu____1684 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname in
                                                    if uu____1684
                                                    then
                                                      let uu____1687 =
                                                        let uu____1690 =
                                                          let uu____1691 =
                                                            let uu____1692 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args in
                                                            FStar_Pervasives_Native.fst
                                                              uu____1692 in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____1691 in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____1690 in
                                                      FStar_Syntax_Util.arrow
                                                        bs uu____1687
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____1708 ->
                                                    act1.FStar_Syntax_Syntax.action_typ in
                                              let uu____1709 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env3 act_typ in
                                              (match uu____1709 with
                                               | (act_typ1, uu____1717, g_t)
                                                   ->
                                                   let env' =
                                                     let uu___75_1720 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env3 act_typ1 in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.dep_graph
                                                         =
                                                         (uu___75_1720.FStar_TypeChecker_Env.dep_graph)
                                                     } in
                                                   ((let uu____1722 =
                                                       FStar_TypeChecker_Env.debug
                                                         env3
                                                         (FStar_Options.Other
                                                            "ED") in
                                                     if uu____1722
                                                     then
                                                       let uu____1723 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name in
                                                       let uu____1724 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn in
                                                       let uu____1725 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1 in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____1723
                                                         uu____1724
                                                         uu____1725
                                                     else ());
                                                    (let uu____1727 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn in
                                                     match uu____1727 with
                                                     | (act_defn, uu____1735,
                                                        g_a) ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.Delta_constant]
                                                             env3 act_defn in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.UnfoldUntil
                                                                FStar_Syntax_Syntax.Delta_constant;
                                                             FStar_TypeChecker_Normalize.Eager_unfolding;
                                                             FStar_TypeChecker_Normalize.Beta]
                                                             env3 act_typ1 in
                                                         let uu____1739 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2 in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs, c) ->
                                                               let uu____1767
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs c in
                                                               (match uu____1767
                                                                with
                                                                | (bs1,
                                                                   uu____1777)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____1784
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1784 in
                                                                    let uu____1787
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k in
                                                                    (match uu____1787
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____1799,
                                                                    g) ->
                                                                    (k1, g)))
                                                           | uu____1801 ->
                                                               let uu____1802
                                                                 =
                                                                 let uu____1807
                                                                   =
                                                                   let uu____1808
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                   let uu____1809
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____1808
                                                                    uu____1809 in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____1807) in
                                                               FStar_Errors.raise_error
                                                                 uu____1802
                                                                 act_defn1.FStar_Syntax_Syntax.pos in
                                                         (match uu____1739
                                                          with
                                                          | (expected_k, g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env3
                                                                  act_typ2
                                                                  expected_k in
                                                              ((let uu____1818
                                                                  =
                                                                  let uu____1819
                                                                    =
                                                                    let uu____1820
                                                                    =
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Rel.conj_guard
                                                                    g_k
                                                                    uu____1820 in
                                                                  FStar_TypeChecker_Rel.conj_guard
                                                                    g_a
                                                                    uu____1819 in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env3
                                                                  uu____1818);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____1824
                                                                    =
                                                                    let uu____1825
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____1825.FStar_Syntax_Syntax.n in
                                                                  match uu____1824
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs, c)
                                                                    ->
                                                                    let uu____1848
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                    (match uu____1848
                                                                    with
                                                                    | 
                                                                    (bs1, c1)
                                                                    ->
                                                                    let uu____1857
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____1857
                                                                    with
                                                                    | 
                                                                    (a1, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1879
                                                                    =
                                                                    let uu____1880
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1 in
                                                                    [uu____1880] in
                                                                    let uu____1881
                                                                    =
                                                                    let uu____1890
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1890] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1879;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1881;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1891
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1891))
                                                                  | uu____1894
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                let uu____1897
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____1899
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____1899)) in
                                                                match uu____1897
                                                                with
                                                                | (univs1,
                                                                   act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.Beta]
                                                                    env3
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4 in
                                                                    let uu___76_1908
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___76_1908.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___76_1908.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___76_1908.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))) in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action) in
                                      (repr, bind_repr, return_repr, actions) in
                                match uu____1122 with
                                | (repr, bind_repr, return_repr, actions) ->
                                    let t0 =
                                      let uu____1932 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1932 in
                                    let uu____1935 =
                                      let uu____1942 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____1942 with
                                      | (gen_univs, t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1963 ->
                                               let uu____1966 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____1972 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____1972 =
                                                             (Prims.parse_int "0"))
                                                      gen_univs
                                                      annotated_univ_names) in
                                               if uu____1966
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1982 =
                                                    let uu____1987 =
                                                      let uu____1988 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names) in
                                                      let uu____1989 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs) in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1988 uu____1989 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1987) in
                                                  FStar_Errors.raise_error
                                                    uu____1982
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                    (match uu____1935 with
                                     | (univs1, t) ->
                                         let signature1 =
                                           let uu____2003 =
                                             let uu____2008 =
                                               let uu____2009 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____2009.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____2008) in
                                           match uu____2003 with
                                           | ([], uu____2012) -> t
                                           | (uu____2023,
                                              FStar_Syntax_Syntax.Tm_arrow
                                              (uu____2024, c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____2042 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____2059 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____2059 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____2064 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____2066 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____2066))
                                                && (m <> n1) in
                                            if uu____2064
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____2082 =
                                                  FStar_Util.string_of_int m in
                                                let uu____2089 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____2090 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2082 uu____2089
                                                  uu____2090 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____2100 =
                                             close1
                                               (~- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____2100 with
                                           | (univs2, defn) ->
                                               let uu____2107 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____2107 with
                                                | (univs', typ) ->
                                                    let uu___77_2115 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___77_2115.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___77_2115.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___77_2115.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___78_2118 = ed2 in
                                           let uu____2119 =
                                             close1 (Prims.parse_int "0")
                                               return_wp in
                                           let uu____2120 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp in
                                           let uu____2121 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1 in
                                           let uu____2122 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp in
                                           let uu____2123 =
                                             close1 (Prims.parse_int "0")
                                               stronger in
                                           let uu____2124 =
                                             close1 (Prims.parse_int "1")
                                               close_wp in
                                           let uu____2125 =
                                             close1 (Prims.parse_int "0")
                                               assert_p in
                                           let uu____2126 =
                                             close1 (Prims.parse_int "0")
                                               assume_p in
                                           let uu____2127 =
                                             close1 (Prims.parse_int "0")
                                               null_wp in
                                           let uu____2128 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp in
                                           let uu____2129 =
                                             let uu____2130 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____2130 in
                                           let uu____2141 =
                                             close1 (Prims.parse_int "0")
                                               return_repr in
                                           let uu____2142 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr in
                                           let uu____2143 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___78_2118.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___78_2118.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2119;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2120;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2121;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2122;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2123;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2124;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2125;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2126;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2127;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2128;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2129;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2141;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2142;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2143;
                                             FStar_Syntax_Syntax.eff_attrs =
                                               (uu___78_2118.FStar_Syntax_Syntax.eff_attrs)
                                           } in
                                         ((let uu____2147 =
                                             (FStar_TypeChecker_Env.debug
                                                env2 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env2)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____2147
                                           then
                                             let uu____2148 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____2148
                                           else ());
                                          ed3))))))))
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list, FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun ed ->
      let uu____2170 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____2170 with
      | (effect_binders_un, signature_un) ->
          let uu____2187 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____2187 with
           | (effect_binders, env1, uu____2206) ->
               let uu____2207 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____2207 with
                | (signature, uu____2223) ->
                    let raise_error1 uu____2238 =
                      match uu____2238 with
                      | (e, err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2264 ->
                           match uu____2264 with
                           | (bv, qual) ->
                               let uu____2275 =
                                 let uu___79_2276 = bv in
                                 let uu____2277 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___79_2276.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___79_2276.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2277
                                 } in
                               (uu____2275, qual)) effect_binders in
                    let uu____2280 =
                      let uu____2287 =
                        let uu____2288 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2288.FStar_Syntax_Syntax.n in
                      match uu____2287 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a, uu____2298)::[], effect_marker) ->
                          (a, effect_marker)
                      | uu____2320 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature") in
                    (match uu____2280 with
                     | (a, effect_marker) ->
                         let a1 =
                           let uu____2344 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2344
                           then
                             let uu____2345 =
                               let uu____2348 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2348 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2345
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2388 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2388 with
                           | (t2, comp, uu____2401) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2410 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2410 with
                          | (repr, _comp) ->
                              ((let uu____2432 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2432
                                then
                                  let uu____2433 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2433
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let uu____2437 =
                                  recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____2439 =
                                    let uu____2440 =
                                      let uu____2441 =
                                        let uu____2456 =
                                          let uu____2463 =
                                            let uu____2468 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2469 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2468, uu____2469) in
                                          [uu____2463] in
                                        (wp_type, uu____2456) in
                                      FStar_Syntax_Syntax.Tm_app uu____2441 in
                                    mk1 uu____2440 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2439 in
                                let effect_signature =
                                  let binders =
                                    let uu____2494 =
                                      let uu____2499 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2499) in
                                    let uu____2500 =
                                      let uu____2507 =
                                        let uu____2508 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2508
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2507] in
                                    uu____2494 :: uu____2500 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let uu____2516 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1 in
                                  let uu____2579 = item in
                                  match uu____2579 with
                                  | (u_item, item1) ->
                                      let uu____2600 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2600 with
                                       | (item2, item_comp) ->
                                           ((let uu____2616 =
                                               let uu____2617 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2617 in
                                             if uu____2616
                                             then
                                               let uu____2618 =
                                                 let uu____2623 =
                                                   let uu____2624 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2625 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2624 uu____2625 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2623) in
                                               FStar_Errors.raise_err
                                                 uu____2618
                                             else ());
                                            (let uu____2627 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2627 with
                                             | (item_t, item_wp, item_elab)
                                                 ->
                                                 let uu____2645 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let uu____2646 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____2647 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2647 with
                                | (dmff_env1, uu____2671, bind_wp, bind_elab)
                                    ->
                                    let uu____2674 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2674 with
                                     | (dmff_env2, uu____2698, return_wp,
                                        return_elab) ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____2705 =
                                             let uu____2706 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2706.FStar_Syntax_Syntax.n in
                                           match uu____2705 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____2750 =
                                                 let uu____2765 =
                                                   let uu____2770 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2770 in
                                                 match uu____2765 with
                                                 | (b11::b21::[], body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2834 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____2750 with
                                                | (b11, b21, body1) ->
                                                    let env0 =
                                                      let uu____2873 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2873 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____2890 =
                                                          let uu____2891 =
                                                            let uu____2906 =
                                                              let uu____2913
                                                                =
                                                                let uu____2918
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____2919
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____2918,
                                                                  uu____2919) in
                                                              [uu____2913] in
                                                            (wp_type,
                                                              uu____2906) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2891 in
                                                        mk1 uu____2890 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____2934 =
                                                      let uu____2943 =
                                                        let uu____2944 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2944 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2943 in
                                                    (match uu____2934 with
                                                     | (bs1, body2, what') ->
                                                         let fail1 uu____2965
                                                           =
                                                           let error_msg =
                                                             let uu____2967 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____2968 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____2967
                                                               uu____2968 in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg) in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                               -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____2973
                                                                   =
                                                                   let uu____2974
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                                   Prims.op_Negation
                                                                    uu____2974 in
                                                                 if
                                                                   uu____2973
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____2976
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    fail1 ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____2976
                                                                   (fun a239
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               FStar_TypeChecker_DMFF.double_star
                                                                 t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu____3001 =
                                                               let uu____3006
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp in
                                                               let uu____3007
                                                                 =
                                                                 let uu____3008
                                                                   =
                                                                   let uu____3015
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                   (uu____3015,
                                                                    FStar_Pervasives_Native.None) in
                                                                 [uu____3008] in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____3006
                                                                 uu____3007 in
                                                             uu____3001
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange in
                                                           let uu____3040 =
                                                             let uu____3041 =
                                                               let uu____3048
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____3048] in
                                                             b11 ::
                                                               uu____3041 in
                                                           let uu____3053 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____3040
                                                             uu____3053
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____3054 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let return_wp1 =
                                           let uu____3056 =
                                             let uu____3057 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____3057.FStar_Syntax_Syntax.n in
                                           match uu____3056 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____3101 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____3101
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____3114 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let bind_wp1 =
                                           let uu____3116 =
                                             let uu____3117 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____3117.FStar_Syntax_Syntax.n in
                                           match uu____3116 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders, body, what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None in
                                               let uu____3144 =
                                                 let uu____3145 =
                                                   let uu____3148 =
                                                     let uu____3149 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____3149 in
                                                   [uu____3148] in
                                                 FStar_List.append uu____3145
                                                   binders in
                                               FStar_Syntax_Util.abs
                                                 uu____3144 body what
                                           | uu____3150 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind") in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____3170 =
                                                let uu____3171 =
                                                  let uu____3172 =
                                                    let uu____3187 =
                                                      let uu____3188 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3188 in
                                                    (t, uu____3187) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3172 in
                                                mk1 uu____3171 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3170) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3222 = f a2 in
                                               [uu____3222]
                                           | x::xs ->
                                               let uu____3227 =
                                                 apply_last1 f xs in
                                               x :: uu____3227 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____3249 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3249 with
                                           | FStar_Pervasives_Native.Some
                                               (_us, _t) ->
                                               ((let uu____3279 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3279
                                                 then
                                                   let uu____3280 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3280
                                                 else ());
                                                (let uu____3282 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3282))
                                           | FStar_Pervasives_Native.None ->
                                               let uu____3291 =
                                                 let uu____3296 = mk_lid name in
                                                 let uu____3297 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3296 uu____3297 in
                                               (match uu____3291 with
                                                | (sigelt, fv) ->
                                                    ((let uu____3301 =
                                                        let uu____3304 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____3304 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3301);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3517 =
                                             let uu____3520 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3521 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3520 :: uu____3521 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3517);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3735 =
                                               let uu____3738 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3739 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3738 :: uu____3739 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3735);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3950 =
                                                FStar_List.fold_left
                                                  (fun uu____3990 ->
                                                     fun action ->
                                                       match uu____3990 with
                                                       | (dmff_env3, actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____4011 =
                                                             let uu____4018 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____4018
                                                               params_un in
                                                           (match uu____4011
                                                            with
                                                            | (action_params,
                                                               env',
                                                               uu____4027) ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____4047
                                                                    ->
                                                                    match uu____4047
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    qual) ->
                                                                    let uu____4058
                                                                    =
                                                                    let uu___80_4059
                                                                    = bv in
                                                                    let uu____4060
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___80_4059.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___80_4059.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____4060
                                                                    } in
                                                                    (uu____4058,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____4064
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____4064
                                                                 with
                                                                 | (dmff_env4,
                                                                    action_t,
                                                                    action_wp,
                                                                    action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____4094
                                                                    ->
                                                                    let uu____4095
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____4095 in
                                                                    ((
                                                                    let uu____4099
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____4099
                                                                    then
                                                                    let uu____4100
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____4101
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____4102
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____4103
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____4100
                                                                    uu____4101
                                                                    uu____4102
                                                                    uu____4103
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4110
                                                                    =
                                                                    let uu___81_4111
                                                                    = action in
                                                                    let uu____4112
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____4113
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___81_4111.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___81_4111.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___81_4111.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____4112;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____4113
                                                                    } in
                                                                    uu____4110
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____4107))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3950 with
                                              | (dmff_env3, actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____4146 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____4147 =
                                                        let uu____4150 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____4150] in
                                                      uu____4146 ::
                                                        uu____4147 in
                                                    let uu____4151 =
                                                      let uu____4152 =
                                                        let uu____4153 =
                                                          let uu____4154 =
                                                            let uu____4169 =
                                                              let uu____4176
                                                                =
                                                                let uu____4181
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____4182
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____4181,
                                                                  uu____4182) in
                                                              [uu____4176] in
                                                            (repr,
                                                              uu____4169) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4154 in
                                                        mk1 uu____4153 in
                                                      let uu____4197 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____4152
                                                        uu____4197 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____4151
                                                      FStar_Pervasives_Native.None in
                                                  let uu____4198 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr2 =
                                                    register "repr" repr1 in
                                                  let uu____4200 =
                                                    let uu____4207 =
                                                      let uu____4208 =
                                                        let uu____4211 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____4211 in
                                                      uu____4208.FStar_Syntax_Syntax.n in
                                                    match uu____4207 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,
                                                         arrow1, uu____4221)
                                                        ->
                                                        let uu____4250 =
                                                          let uu____4267 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1 in
                                                          match uu____4267
                                                          with
                                                          | (b::bs, body) ->
                                                              (b, bs, body)
                                                          | uu____4325 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____4250
                                                         with
                                                         | (type_param1,
                                                            effect_param1,
                                                            arrow2) ->
                                                             let uu____4375 =
                                                               let uu____4376
                                                                 =
                                                                 let uu____4379
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____4379 in
                                                               uu____4376.FStar_Syntax_Syntax.n in
                                                             (match uu____4375
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,
                                                                   c)
                                                                  ->
                                                                  let uu____4404
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____4404
                                                                   with
                                                                   | 
                                                                   (wp_binders1,
                                                                    c1) ->
                                                                    let uu____4417
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4442
                                                                    ->
                                                                    match uu____4442
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    uu____4448)
                                                                    ->
                                                                    let uu____4449
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____4450
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____4449
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____4417
                                                                    with
                                                                    | 
                                                                    (pre_args,
                                                                    post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4514
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4514 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4519
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4527
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4527 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____4532
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____4535
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____4532,
                                                                    uu____4535)))
                                                              | uu____4542 ->
                                                                  let uu____4543
                                                                    =
                                                                    let uu____4548
                                                                    =
                                                                    let uu____4549
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4549 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4548) in
                                                                  raise_error1
                                                                    uu____4543))
                                                    | uu____4556 ->
                                                        let uu____4557 =
                                                          let uu____4562 =
                                                            let uu____4563 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____4563 in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____4562) in
                                                        raise_error1
                                                          uu____4557 in
                                                  (match uu____4200 with
                                                   | (pre, post) ->
                                                       ((let uu____4587 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____4589 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____4591 =
                                                           register "wp"
                                                             wp_type in
                                                         ());
                                                        (let ed1 =
                                                           let uu___82_4593 =
                                                             ed in
                                                           let uu____4594 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____4595 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature in
                                                           let uu____4596 =
                                                             let uu____4597 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____4597) in
                                                           let uu____4604 =
                                                             let uu____4605 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4605) in
                                                           let uu____4612 =
                                                             apply_close
                                                               repr2 in
                                                           let uu____4613 =
                                                             let uu____4614 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4614) in
                                                           let uu____4621 =
                                                             let uu____4622 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4622) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4594;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4595;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4596;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4604;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4612;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4613;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4621;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___82_4593.FStar_Syntax_Syntax.eff_attrs)
                                                           } in
                                                         let uu____4629 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4629
                                                         with
                                                         | (sigelts', ed2) ->
                                                             ((let uu____4647
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4647
                                                               then
                                                                 let uu____4648
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4648
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____4660
                                                                    =
                                                                    let uu____4663
                                                                    =
                                                                    let uu____4672
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4672) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4663 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4660;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4687
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4687
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4689
                                                                 =
                                                                 let uu____4692
                                                                   =
                                                                   let uu____4695
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4695 in
                                                                 FStar_List.append
                                                                   uu____4692
                                                                   sigelts' in
                                                               (uu____4689,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t :
  'Auu____4815 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4815 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let err_range =
            let uu____4850 = FStar_List.hd ses in
            uu____4850.FStar_Syntax_Syntax.sigrng in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____4855 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1, uu____4859, [], t, uu____4861, uu____4862);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4864;
               FStar_Syntax_Syntax.sigattrs = uu____4865;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,
                                                                  uu____4867,
                                                                  _t_top,
                                                                  _lex_t_top,
                                                                  _0_17,
                                                                  uu____4870);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4872;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4873;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons, uu____4875, _t_cons, _lex_t_cons, _0_18,
                    uu____4878);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4880;
                 FStar_Syntax_Syntax.sigattrs = uu____4881;_}::[]
               when
               ((_0_17 = (Prims.parse_int "0")) &&
                  (_0_18 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r) in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1) in
               let lex_top_t =
                 let uu____4940 =
                   let uu____4947 =
                     let uu____4948 =
                       let uu____4955 =
                         let uu____4956 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1 in
                         FStar_Syntax_Syntax.fvar uu____4956
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4955, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4948 in
                   FStar_Syntax_Syntax.mk uu____4947 in
                 uu____4940 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let lex_cons_t =
                 let a =
                   let uu____4974 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4974 in
                 let hd1 =
                   let uu____4976 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4976 in
                 let tl1 =
                   let uu____4978 =
                     let uu____4979 =
                       let uu____4986 =
                         let uu____4987 =
                           let uu____4994 =
                             let uu____4995 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2 in
                             FStar_Syntax_Syntax.fvar uu____4995
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4994, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4987 in
                       FStar_Syntax_Syntax.mk uu____4986 in
                     uu____4979 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4978 in
                 let res =
                   let uu____5004 =
                     let uu____5011 =
                       let uu____5012 =
                         let uu____5019 =
                           let uu____5020 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2 in
                           FStar_Syntax_Syntax.fvar uu____5020
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____5019,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____5012 in
                     FStar_Syntax_Syntax.mk uu____5011 in
                   uu____5004 FStar_Pervasives_Native.None r2 in
                 let uu____5026 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____5026 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let uu____5065 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____5065;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____5070 ->
               let err_msg =
                 let uu____5074 =
                   let uu____5075 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____5075 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____5074 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.formula ->
      FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun phi ->
      fun r ->
        let env1 = FStar_TypeChecker_Env.set_range env r in
        let uu____5096 = FStar_Syntax_Util.type_u () in
        match uu____5096 with
        | (k, uu____5102) ->
            let phi1 =
              let uu____5104 = tc_check_trivial_guard env1 phi k in
              FStar_All.pipe_right uu____5104
                (FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
            (FStar_TypeChecker_Util.check_uvars r phi1; phi1)
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt, FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____5145 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____5145 with
          | (sig_bndle, tcs, datas) ->
              let data_ops_ses =
                let uu____5176 =
                  FStar_List.map
                    (FStar_TypeChecker_TcInductive.mk_data_operations quals
                       env1 tcs) datas in
                FStar_All.pipe_right uu____5176 FStar_List.flatten in
              ((let uu____5190 =
                  (FStar_Options.no_positivity ()) ||
                    (let uu____5192 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     Prims.op_Negation uu____5192) in
                if uu____5190
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
                          let uu____5203 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, uu____5213, uu____5214, uu____5215,
                                 uu____5216, uu____5217)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____5226 -> failwith "Impossible!" in
                          match uu____5203 with
                          | (lid, r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____5239 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid, uu____5243, uu____5244, uu____5245, uu____5246,
                         uu____5247)
                        -> lid
                    | uu____5256 -> failwith "Impossible" in
                  FStar_List.existsb
                    (fun s -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    FStar_TypeChecker_TcInductive.early_prims_inductives in
                let is_noeq =
                  FStar_List.existsb (fun q -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let res =
                  let uu____5269 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____5269
                  then (sig_bndle, data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 in
                     (sig_bndle, (FStar_List.append ses1 data_ops_ses))) in
                (let uu____5291 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en ->
    let env =
      let uu____5298 = FStar_Options.using_facts_from () in
      FStar_TypeChecker_Env.set_proof_ns uu____5298 en in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun se ->
    FStar_List.tryPick (FStar_ToSyntax_ToSyntax.get_fail_attr true)
      se.FStar_Syntax_Syntax.sigattrs
let list_of_option :
  'Auu____5319 .
    'Auu____5319 FStar_Pervasives_Native.option -> 'Auu____5319 Prims.list
  =
  fun uu___62_5328 ->
    match uu___62_5328 with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some x -> [x]
let (check_multi_contained :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option)
  =
  fun l1 ->
    fun l2 ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____5387 = collect1 tl1 in
            (match uu____5387 with
             | [] -> [(hd1, (Prims.parse_int "1"))]
             | (h, n1)::t ->
                 if h = hd1
                 then (h, (n1 + (Prims.parse_int "1"))) :: t
                 else (hd1, (Prims.parse_int "1")) :: (h, n1) :: t) in
      let summ l =
        let l3 = FStar_List.sortWith (fun x -> fun y -> x - y) l in
        collect1 l3 in
      let l11 = summ l1 in
      let l21 = summ l2 in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], uu____5544) -> FStar_Pervasives_Native.None
        | ((e, n1)::uu____5575, []) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) when hd1 > hd2 -> aux l12 tl2
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) when hd1 < hd2 ->
            FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) when hd1 = hd2 ->
            if n1 <> n2
            then FStar_Pervasives_Native.Some (hd1, n1, n2)
            else aux tl1 tl2 in
      aux l11 l21
let rec (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_Syntax_Syntax.sigelt Prims.list) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let env1 = set_hint_correlator env se in
      (let uu____5787 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____5787
       then
         let uu____5788 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____5788
       else ());
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let uu____5791 = get_fail_se se in
       match uu____5791 with
       | FStar_Pervasives_Native.Some errnos ->
           ((let uu____5810 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5810
             then
               let uu____5811 =
                 let uu____5812 =
                   FStar_List.map FStar_Util.string_of_int errnos in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____5812 in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____5811
             else ());
            (let errs =
               FStar_Errors.catch_errors (fun uu____5830 -> tc_decl' env1 se) in
             (let uu____5832 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____5832
              then
                (FStar_Util.print_string ">> Got issues:\n";
                 FStar_List.iter FStar_Errors.print_issue errs;
                 FStar_Util.print_string ">> //Got issues:\n")
              else ());
             (let uu____5836 =
                let uu____5851 =
                  let uu____5860 =
                    FStar_List.concatMap
                      (fun i -> list_of_option i.FStar_Errors.issue_number)
                      errs in
                  check_multi_contained errnos uu____5860 in
                (errs, uu____5851) in
              match uu____5836 with
              | ([], uu____5883) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   FStar_Errors.raise_error
                     (FStar_Errors.Error_DidNotFail,
                       "This top-level definition was expected to fail, but it succeeded")
                     se.FStar_Syntax_Syntax.sigrng)
              | (uu____5911, FStar_Pervasives_Native.Some (e, n1, n2)) ->
                  (FStar_List.iter FStar_Errors.print_issue errs;
                   (let uu____5934 =
                      let uu____5939 =
                        let uu____5940 = FStar_Util.string_of_int e in
                        let uu____5941 = FStar_Util.string_of_int n1 in
                        let uu____5942 = FStar_Util.string_of_int n2 in
                        FStar_Util.format3
                          "This top-level definition was expected to raise Error #%s %s times, but it raised it %s times"
                          uu____5940 uu____5941 uu____5942 in
                      (FStar_Errors.Error_DidNotFail, uu____5939) in
                    FStar_Errors.raise_error uu____5934
                      se.FStar_Syntax_Syntax.sigrng))
              | (uu____5951, FStar_Pervasives_Native.None) -> ([], []))))
       | FStar_Pervasives_Native.None -> tc_decl' env1 se)
and (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_Syntax_Syntax.sigelt Prims.list) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let r = se.FStar_Syntax_Syntax.sigrng in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____5995 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____6020 ->
          failwith "Impossible bare data-constructor"
      | FStar_Syntax_Syntax.Sig_bundle (ses, lids) when
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
          ->
          let env1 = FStar_TypeChecker_Env.set_range env r in
          let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids in
          ([se1], [])
      | FStar_Syntax_Syntax.Sig_bundle (ses, lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r in
          let ses1 =
            let uu____6075 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env1) in
            if uu____6075
            then
              let ses1 =
                let uu____6081 =
                  let uu____6082 =
                    let uu____6083 =
                      tc_inductive
                        (let uu___83_6092 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___83_6092.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___83_6092.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___83_6092.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___83_6092.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___83_6092.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___83_6092.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___83_6092.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___83_6092.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___83_6092.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___83_6092.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___83_6092.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___83_6092.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___83_6092.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___83_6092.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___83_6092.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___83_6092.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___83_6092.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___83_6092.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___83_6092.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___83_6092.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___83_6092.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___83_6092.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___83_6092.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___83_6092.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___83_6092.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___83_6092.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___83_6092.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___83_6092.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___83_6092.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___83_6092.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___83_6092.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___83_6092.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___83_6092.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___83_6092.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___83_6092.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___83_6092.FStar_TypeChecker_Env.dep_graph)
                         }) ses se.FStar_Syntax_Syntax.sigquals lids in
                    FStar_All.pipe_right uu____6083
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____6082
                    (FStar_TypeChecker_Normalize.elim_uvars env1) in
                FStar_All.pipe_right uu____6081
                  FStar_Syntax_Util.ses_of_sigbundle in
              ((let uu____6104 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "TwoPhases") in
                if uu____6104
                then
                  let uu____6105 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___84_6108 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___84_6108.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___84_6108.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___84_6108.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___84_6108.FStar_Syntax_Syntax.sigattrs)
                       }) in
                  FStar_Util.print1 "Inductive after phase 1: %s\n"
                    uu____6105
                else ());
               ses1)
            else ses in
          let uu____6115 =
            tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids in
          (match uu____6115 with
           | (sigbndle, projectors_ses) -> ([sigbndle], projectors_ses))
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p r; ([se], []))
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
          let uu____6147 = cps_and_elaborate env ne in
          (match uu____6147 with
           | (ses, ne1, lift_from_pure_opt) ->
               let effect_and_lift_ses =
                 match lift_from_pure_opt with
                 | FStar_Pervasives_Native.Some lift ->
                     [(let uu___85_6184 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___85_6184.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___85_6184.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___85_6184.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___85_6184.FStar_Syntax_Syntax.sigattrs)
                       });
                     lift]
                 | FStar_Pervasives_Native.None ->
                     [(let uu___86_6186 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___86_6186.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___86_6186.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___86_6186.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___86_6186.FStar_Syntax_Syntax.sigattrs)
                       })] in
               ([], (FStar_List.append ses effect_and_lift_ses)))
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let ne1 =
            let uu____6193 =
              (FStar_Options.use_two_phase_tc ()) &&
                (FStar_TypeChecker_Env.should_verify env) in
            if uu____6193
            then
              let ne1 =
                let uu____6195 =
                  let uu____6196 =
                    let uu____6197 =
                      tc_eff_decl
                        (let uu___87_6200 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___87_6200.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___87_6200.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___87_6200.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___87_6200.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___87_6200.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___87_6200.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___87_6200.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___87_6200.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___87_6200.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___87_6200.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___87_6200.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___87_6200.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___87_6200.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___87_6200.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___87_6200.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___87_6200.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___87_6200.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___87_6200.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___87_6200.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___87_6200.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___87_6200.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___87_6200.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___87_6200.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___87_6200.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___87_6200.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___87_6200.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___87_6200.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___87_6200.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___87_6200.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___87_6200.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___87_6200.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___87_6200.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___87_6200.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___87_6200.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___87_6200.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___87_6200.FStar_TypeChecker_Env.dep_graph)
                         }) ne in
                    FStar_All.pipe_right uu____6197
                      (fun ne1 ->
                         let uu___88_6204 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ne1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___88_6204.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___88_6204.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___88_6204.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___88_6204.FStar_Syntax_Syntax.sigattrs)
                         }) in
                  FStar_All.pipe_right uu____6196
                    (FStar_TypeChecker_Normalize.elim_uvars env) in
                FStar_All.pipe_right uu____6195
                  FStar_Syntax_Util.eff_decl_of_new_effect in
              ((let uu____6206 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "TwoPhases") in
                if uu____6206
                then
                  let uu____6207 =
                    FStar_Syntax_Print.sigelt_to_string
                      (let uu___89_6210 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_new_effect ne1);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___89_6210.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___89_6210.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___89_6210.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___89_6210.FStar_Syntax_Syntax.sigattrs)
                       }) in
                  FStar_Util.print1 "Effect decl after phase 1: %s\n"
                    uu____6207
                else ());
               ne1)
            else ne in
          let ne2 = tc_eff_decl env ne1 in
          let se1 =
            let uu___90_6215 = se in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_new_effect ne2);
              FStar_Syntax_Syntax.sigrng =
                (uu___90_6215.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals =
                (uu___90_6215.FStar_Syntax_Syntax.sigquals);
              FStar_Syntax_Syntax.sigmeta =
                (uu___90_6215.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs =
                (uu___90_6215.FStar_Syntax_Syntax.sigattrs)
            } in
          ([se1], [])
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let ed_src =
            FStar_TypeChecker_Env.get_effect_decl env
              sub1.FStar_Syntax_Syntax.source in
          let ed_tgt =
            FStar_TypeChecker_Env.get_effect_decl env
              sub1.FStar_Syntax_Syntax.target in
          let uu____6223 =
            let uu____6230 =
              FStar_TypeChecker_Env.lookup_effect_lid env
                sub1.FStar_Syntax_Syntax.source in
            monad_signature env sub1.FStar_Syntax_Syntax.source uu____6230 in
          (match uu____6223 with
           | (a, wp_a_src) ->
               let uu____6245 =
                 let uu____6252 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____6252 in
               (match uu____6245 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____6268 =
                        let uu____6271 =
                          let uu____6272 =
                            let uu____6279 = FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____6279) in
                          FStar_Syntax_Syntax.NT uu____6272 in
                        [uu____6271] in
                      FStar_Syntax_Subst.subst uu____6268 wp_b_tgt in
                    let expected_k =
                      let uu____6283 =
                        let uu____6290 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____6291 =
                          let uu____6294 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____6294] in
                        uu____6290 :: uu____6291 in
                      let uu____6295 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____6283 uu____6295 in
                    let repr_type eff_name a1 wp =
                      let no_reify l =
                        let uu____6324 =
                          let uu____6329 =
                            FStar_Util.format1 "Effect %s cannot be reified"
                              l.FStar_Ident.str in
                          (FStar_Errors.Fatal_EffectCannotBeReified,
                            uu____6329) in
                        let uu____6330 = FStar_TypeChecker_Env.get_range env in
                        FStar_Errors.raise_error uu____6324 uu____6330 in
                      let uu____6333 =
                        FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                      match uu____6333 with
                      | FStar_Pervasives_Native.None -> no_reify eff_name
                      | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                          let repr =
                            FStar_TypeChecker_Env.inst_effect_fun_with
                              [FStar_Syntax_Syntax.U_unknown] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____6365 =
                            let uu____6366 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable) in
                            Prims.op_Negation uu____6366 in
                          if uu____6365
                          then no_reify eff_name
                          else
                            (let uu____6372 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____6373 =
                               let uu____6380 =
                                 let uu____6381 =
                                   let uu____6396 =
                                     let uu____6399 =
                                       FStar_Syntax_Syntax.as_arg a1 in
                                     let uu____6400 =
                                       let uu____6403 =
                                         FStar_Syntax_Syntax.as_arg wp in
                                       [uu____6403] in
                                     uu____6399 :: uu____6400 in
                                   (repr, uu____6396) in
                                 FStar_Syntax_Syntax.Tm_app uu____6381 in
                               FStar_Syntax_Syntax.mk uu____6380 in
                             uu____6373 FStar_Pervasives_Native.None
                               uu____6372) in
                    let uu____6409 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____6461 =
                            if
                              (FStar_List.length uvs) > (Prims.parse_int "0")
                            then
                              let uu____6470 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____6470 with
                              | (usubst, uvs1) ->
                                  let uu____6493 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____6494 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____6493, uu____6494)
                            else (env, lift_wp) in
                          (match uu____6461 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if
                                   (FStar_List.length uvs) =
                                     (Prims.parse_int "0")
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k in
                                    let uu____6507 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____6507)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____6534 =
                            if
                              (FStar_List.length what) >
                                (Prims.parse_int "0")
                            then
                              let uu____6547 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____6547 with
                              | (usubst, uvs) ->
                                  let uu____6572 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____6572)
                            else ([], lift) in
                          (match uu____6534 with
                           | (uvs, lift1) ->
                               ((let uu____6591 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____6591
                                 then
                                   let uu____6592 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____6592
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____6595 =
                                   let uu____6602 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____6602 lift1 in
                                 match uu____6595 with
                                 | (lift2, comp, uu____6611) ->
                                     let uu____6612 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____6612 with
                                      | (uu____6625, lift_wp, lift_elab) ->
                                          let lift_wp1 =
                                            recheck_debug "lift-wp" env
                                              lift_wp in
                                          let lift_elab1 =
                                            recheck_debug "lift-elab" env
                                              lift_elab in
                                          if
                                            (FStar_List.length uvs) =
                                              (Prims.parse_int "0")
                                          then
                                            let uu____6636 =
                                              let uu____6639 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____6639 in
                                            let uu____6640 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____6636, uu____6640)
                                          else
                                            (let uu____6644 =
                                               let uu____6653 =
                                                 let uu____6660 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____6660) in
                                               FStar_Pervasives_Native.Some
                                                 uu____6653 in
                                             let uu____6669 =
                                               let uu____6676 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____6676) in
                                             (uu____6644, uu____6669)))))) in
                    (match uu____6409 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___91_6708 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___91_6708.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___91_6708.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___91_6708.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___91_6708.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___91_6708.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___91_6708.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___91_6708.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___91_6708.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___91_6708.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___91_6708.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___91_6708.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___91_6708.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___91_6708.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___91_6708.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___91_6708.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___91_6708.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___91_6708.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___91_6708.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___91_6708.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___91_6708.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___91_6708.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___91_6708.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___91_6708.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___91_6708.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___91_6708.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___91_6708.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___91_6708.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___91_6708.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___91_6708.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___91_6708.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___91_6708.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___91_6708.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___91_6708.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___91_6708.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___91_6708.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___91_6708.FStar_TypeChecker_Env.dep_graph)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____6726 =
                                 let uu____6731 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____6731 with
                                 | (usubst, uvs1) ->
                                     let uu____6754 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____6755 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____6754, uu____6755) in
                               (match uu____6726 with
                                | (env2, lift2) ->
                                    let uu____6760 =
                                      let uu____6767 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____6767 in
                                    (match uu____6760 with
                                     | (a1, wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1 in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1 in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a in
                                         let repr_f =
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Normalize.EraseUniverses;
                                               FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp) in
                                           let lift_wp_a =
                                             let uu____6791 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             let uu____6792 =
                                               let uu____6799 =
                                                 let uu____6800 =
                                                   let uu____6815 =
                                                     let uu____6818 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ in
                                                     let uu____6819 =
                                                       let uu____6822 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ in
                                                       [uu____6822] in
                                                     uu____6818 :: uu____6819 in
                                                   (lift_wp1, uu____6815) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6800 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6799 in
                                             uu____6792
                                               FStar_Pervasives_Native.None
                                               uu____6791 in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____6831 =
                                             let uu____6838 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____6839 =
                                               let uu____6842 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____6843 =
                                                 let uu____6846 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____6846] in
                                               uu____6842 :: uu____6843 in
                                             uu____6838 :: uu____6839 in
                                           let uu____6847 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow uu____6831
                                             uu____6847 in
                                         let uu____6850 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____6850 with
                                          | (expected_k2, uu____6860,
                                             uu____6861) ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    (Prims.parse_int "0")
                                                then
                                                  check_and_gen env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     tc_check_trivial_guard
                                                       env2 lift2 expected_k2 in
                                                   let uu____6865 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____6865)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____6869 =
                             let uu____6870 =
                               let uu____6871 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____6871
                                 FStar_List.length in
                             uu____6870 <> (Prims.parse_int "1") in
                           if uu____6869
                           then
                             let uu____6884 =
                               let uu____6889 =
                                 let uu____6890 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source in
                                 let uu____6891 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target in
                                 let uu____6892 =
                                   let uu____6893 =
                                     let uu____6894 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____6894
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____6893
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____6890 uu____6891 uu____6892 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____6889) in
                             FStar_Errors.raise_error uu____6884 r
                           else ());
                          (let uu____6909 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____6911 =
                                  let uu____6912 =
                                    let uu____6915 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____6915
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____6912
                                    FStar_List.length in
                                uu____6911 <> (Prims.parse_int "1")) in
                           if uu____6909
                           then
                             let uu____6928 =
                               let uu____6933 =
                                 let uu____6934 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source in
                                 let uu____6935 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target in
                                 let uu____6936 =
                                   let uu____6937 =
                                     let uu____6938 =
                                       let uu____6941 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____6941
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____6938
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____6937
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____6934 uu____6935 uu____6936 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____6933) in
                             FStar_Errors.raise_error uu____6928 r
                           else ());
                          (let sub2 =
                             let uu___92_6956 = sub1 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___92_6956.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___92_6956.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp =
                                 (FStar_Pervasives_Native.Some lift_wp);
                               FStar_Syntax_Syntax.lift = lift1
                             } in
                           let se1 =
                             let uu___93_6958 = se in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___93_6958.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___93_6958.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___93_6958.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___93_6958.FStar_Syntax_Syntax.sigattrs)
                             } in
                           ([se1], []))))))
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags1) ->
          let env0 = env in
          let uu____6973 =
            if (FStar_List.length uvs) = (Prims.parse_int "0")
            then (env, uvs, tps, c)
            else
              (let uu____6991 = FStar_Syntax_Subst.univ_var_opening uvs in
               match uu____6991 with
               | (usubst, uvs1) ->
                   let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                   let c1 =
                     let uu____7020 =
                       FStar_Syntax_Subst.shift_subst
                         (FStar_List.length tps1) usubst in
                     FStar_Syntax_Subst.subst_comp uu____7020 c in
                   let uu____7027 =
                     FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                   (uu____7027, uvs1, tps1, c1)) in
          (match uu____6973 with
           | (env1, uvs1, tps1, c1) ->
               let env2 = FStar_TypeChecker_Env.set_range env1 r in
               let uu____7043 = FStar_Syntax_Subst.open_comp tps1 c1 in
               (match uu____7043 with
                | (tps2, c2) ->
                    let uu____7058 =
                      FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                    (match uu____7058 with
                     | (tps3, env3, us) ->
                         let uu____7076 =
                           FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                         (match uu____7076 with
                          | (c3, u, g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env3
                                 g;
                               (let tps4 =
                                  FStar_Syntax_Subst.close_binders tps3 in
                                let c4 =
                                  FStar_Syntax_Subst.close_comp tps4 c3 in
                                let uu____7097 =
                                  let uu____7098 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_arrow
                                         (tps4, c4))
                                      FStar_Pervasives_Native.None r in
                                  FStar_TypeChecker_Util.generalize_universes
                                    env0 uu____7098 in
                                match uu____7097 with
                                | (uvs2, t) ->
                                    let uu____7113 =
                                      let uu____7126 =
                                        let uu____7131 =
                                          let uu____7132 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____7132.FStar_Syntax_Syntax.n in
                                        (tps4, uu____7131) in
                                      match uu____7126 with
                                      | ([], FStar_Syntax_Syntax.Tm_arrow
                                         (uu____7147, c5)) -> ([], c5)
                                      | (uu____7187,
                                         FStar_Syntax_Syntax.Tm_arrow
                                         (tps5, c5)) -> (tps5, c5)
                                      | uu____7214 ->
                                          failwith
                                            "Impossible (t is an arrow)" in
                                    (match uu____7113 with
                                     | (tps5, c5) ->
                                         (if
                                            (FStar_List.length uvs2) <>
                                              (Prims.parse_int "1")
                                          then
                                            (let uu____7258 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 uvs2 t in
                                             match uu____7258 with
                                             | (uu____7263, t1) ->
                                                 let uu____7265 =
                                                   let uu____7270 =
                                                     let uu____7271 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid in
                                                     let uu____7272 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs2)
                                                         FStar_Util.string_of_int in
                                                     let uu____7273 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t1 in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       uu____7271 uu____7272
                                                       uu____7273 in
                                                   (FStar_Errors.Fatal_TooManyUniverse,
                                                     uu____7270) in
                                                 FStar_Errors.raise_error
                                                   uu____7265 r)
                                          else ();
                                          (let se1 =
                                             let uu___94_7276 = se in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                    (lid, uvs2, tps5, c5,
                                                      flags1));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___94_7276.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 (uu___94_7276.FStar_Syntax_Syntax.sigquals);
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___94_7276.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___94_7276.FStar_Syntax_Syntax.sigattrs)
                                             } in
                                           ([se1], []))))))))))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7293, uu____7294, uu____7295) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___63_7299 ->
                  match uu___63_7299 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____7300 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_let (uu____7305, uu____7306) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___63_7314 ->
                  match uu___63_7314 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____7315 -> false))
          -> ([], [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
          let env1 = FStar_TypeChecker_Env.set_range env r in
          ((let uu____7325 = FStar_TypeChecker_Env.lid_exists env1 lid in
            if uu____7325
            then
              let uu____7326 =
                let uu____7331 =
                  let uu____7332 = FStar_Ident.text_of_lid lid in
                  FStar_Util.format1
                    "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                    uu____7332 in
                (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                  uu____7331) in
              FStar_Errors.raise_error uu____7326 r
            else ());
           (let uu____7334 =
              if uvs = []
              then
                let uu____7335 =
                  let uu____7336 = FStar_Syntax_Util.type_u () in
                  FStar_Pervasives_Native.fst uu____7336 in
                check_and_gen env1 t uu____7335
              else
                (let uu____7342 = FStar_Syntax_Subst.open_univ_vars uvs t in
                 match uu____7342 with
                 | (uvs1, t1) ->
                     let env2 =
                       FStar_TypeChecker_Env.push_univ_vars env1 uvs1 in
                     let t2 =
                       let uu____7351 =
                         let uu____7352 = FStar_Syntax_Util.type_u () in
                         FStar_Pervasives_Native.fst uu____7352 in
                       tc_check_trivial_guard env2 t1 uu____7351 in
                     let t3 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.NoFullNorm;
                         FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                         env2 t2 in
                     let uu____7358 =
                       FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                     (uvs1, uu____7358)) in
            match uu____7334 with
            | (uvs1, t1) ->
                let se1 =
                  let uu___95_7374 = se in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                    FStar_Syntax_Syntax.sigrng =
                      (uu___95_7374.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___95_7374.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___95_7374.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___95_7374.FStar_Syntax_Syntax.sigattrs)
                  } in
                ([se1], [])))
      | FStar_Syntax_Syntax.Sig_assume (lid, us, phi) ->
          let uu____7384 = FStar_Syntax_Subst.open_univ_vars us phi in
          (match uu____7384 with
           | (us1, phi1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
               let phi2 =
                 let uu____7401 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1) in
                 if uu____7401
                 then
                   let phi2 =
                     let uu____7403 =
                       tc_assume
                         (let uu___96_7406 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___96_7406.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___96_7406.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___96_7406.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___96_7406.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___96_7406.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___96_7406.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___96_7406.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___96_7406.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___96_7406.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___96_7406.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___96_7406.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___96_7406.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___96_7406.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___96_7406.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___96_7406.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___96_7406.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___96_7406.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___96_7406.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___96_7406.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___96_7406.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___96_7406.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___96_7406.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___96_7406.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___96_7406.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___96_7406.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___96_7406.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___96_7406.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___96_7406.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___96_7406.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___96_7406.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___96_7406.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___96_7406.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___96_7406.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___96_7406.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___96_7406.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___96_7406.FStar_TypeChecker_Env.dep_graph)
                          }) phi1 r in
                     FStar_All.pipe_right uu____7403
                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                          env1) in
                   ((let uu____7408 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____7408
                     then
                       let uu____7409 =
                         FStar_Syntax_Print.term_to_string phi2 in
                       FStar_Util.print1 "Assume after phase 1: %s\n"
                         uu____7409
                     else ());
                    phi2)
                 else phi1 in
               let phi3 = tc_assume env1 phi2 r in
               let uu____7413 =
                 if us1 = []
                 then FStar_TypeChecker_Util.generalize_universes env1 phi3
                 else
                   (let uu____7415 =
                      FStar_Syntax_Subst.close_univ_vars us1 phi3 in
                    (us1, uu____7415)) in
               (match uu____7413 with
                | (us2, phi4) ->
                    ([{
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us2, phi4));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals =
                          (se.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs = []
                      }], [])))
      | FStar_Syntax_Syntax.Sig_main e ->
          let env1 = FStar_TypeChecker_Env.set_range env r in
          let env2 =
            FStar_TypeChecker_Env.set_expected_typ env1
              FStar_Syntax_Syntax.t_unit in
          let uu____7439 = FStar_TypeChecker_TcTerm.tc_term env2 e in
          (match uu____7439 with
           | (e1, c, g1) ->
               let uu____7457 =
                 let uu____7464 =
                   let uu____7467 =
                     FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                   FStar_Pervasives_Native.Some uu____7467 in
                 let uu____7468 =
                   let uu____7473 = FStar_Syntax_Syntax.lcomp_comp c in
                   (e1, uu____7473) in
                 FStar_TypeChecker_TcTerm.check_expected_effect env2
                   uu____7464 uu____7468 in
               (match uu____7457 with
                | (e2, uu____7483, g) ->
                    ((let uu____7486 = FStar_TypeChecker_Rel.conj_guard g1 g in
                      FStar_TypeChecker_Rel.force_trivial_guard env2
                        uu____7486);
                     (let se1 =
                        let uu___97_7488 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_main e2);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___97_7488.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___97_7488.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___97_7488.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___97_7488.FStar_Syntax_Syntax.sigattrs)
                        } in
                      ([se1], [])))))
      | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
          ((let uu____7500 = FStar_Options.debug_any () in
            if uu____7500
            then
              let uu____7501 =
                FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
              let uu____7502 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.print2 "%s: Found splice of (%s)\n" uu____7501
                uu____7502
            else ());
           (let ses = env.FStar_TypeChecker_Env.splice env t in
            let lids' =
              FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses in
            FStar_List.iter
              (fun lid ->
                 let uu____7515 =
                   FStar_List.tryFind (FStar_Ident.lid_equals lid) lids' in
                 match uu____7515 with
                 | FStar_Pervasives_Native.Some uu____7518 -> ()
                 | FStar_Pervasives_Native.None ->
                     let uu____7519 =
                       let uu____7524 =
                         let uu____7525 = FStar_Ident.string_of_lid lid in
                         let uu____7526 =
                           let uu____7527 =
                             FStar_List.map FStar_Ident.string_of_lid lids' in
                           FStar_All.pipe_left (FStar_String.concat ", ")
                             uu____7527 in
                         FStar_Util.format2
                           "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                           uu____7525 uu____7526 in
                       (FStar_Errors.Fatal_SplicedUndef, uu____7524) in
                     FStar_Errors.raise_error uu____7519 r) lids;
            ([], ses)))
      | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
          let env1 = FStar_TypeChecker_Env.set_range env r in
          let check_quals_eq l qopt q =
            match qopt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some q
            | FStar_Pervasives_Native.Some q' ->
                let uu____7588 =
                  ((FStar_List.length q) = (FStar_List.length q')) &&
                    (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                       q') in
                if uu____7588
                then FStar_Pervasives_Native.Some q
                else
                  (let uu____7596 =
                     let uu____7601 =
                       let uu____7602 = FStar_Syntax_Print.lid_to_string l in
                       let uu____7603 = FStar_Syntax_Print.quals_to_string q in
                       let uu____7604 = FStar_Syntax_Print.quals_to_string q' in
                       FStar_Util.format3
                         "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                         uu____7602 uu____7603 uu____7604 in
                     (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                       uu____7601) in
                   FStar_Errors.raise_error uu____7596 r) in
          let rename_parameters lb =
            let rename_in_typ def typ =
              let typ1 = FStar_Syntax_Subst.compress typ in
              let def_bs =
                let uu____7636 =
                  let uu____7637 = FStar_Syntax_Subst.compress def in
                  uu____7637.FStar_Syntax_Syntax.n in
                match uu____7636 with
                | FStar_Syntax_Syntax.Tm_abs
                    (binders, uu____7647, uu____7648) -> binders
                | uu____7669 -> [] in
              match typ1 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                    (val_bs, c);
                  FStar_Syntax_Syntax.pos = r1;
                  FStar_Syntax_Syntax.vars = uu____7679;_} ->
                  let has_auto_name bv =
                    FStar_Util.starts_with
                      (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      FStar_Ident.reserved_prefix in
                  let rec rename_binders1 def_bs1 val_bs1 =
                    match (def_bs1, val_bs1) with
                    | ([], uu____7763) -> val_bs1
                    | (uu____7786, []) -> val_bs1
                    | ((body_bv, uu____7810)::bt, (val_bv, aqual)::vt) ->
                        let uu____7847 = rename_binders1 bt vt in
                        ((match ((has_auto_name body_bv),
                                  (has_auto_name val_bv))
                          with
                          | (true, uu____7863) -> (val_bv, aqual)
                          | (false, true) ->
                              ((let uu___98_7865 = val_bv in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (let uu___99_7868 =
                                       val_bv.FStar_Syntax_Syntax.ppname in
                                     {
                                       FStar_Ident.idText =
                                         ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                       FStar_Ident.idRange =
                                         (uu___99_7868.FStar_Ident.idRange)
                                     });
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_7865.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort =
                                    (uu___98_7865.FStar_Syntax_Syntax.sort)
                                }), aqual)
                          | (false, false) -> (val_bv, aqual))) :: uu____7847 in
                  let uu____7869 =
                    let uu____7876 =
                      let uu____7877 =
                        let uu____7890 = rename_binders1 def_bs val_bs in
                        (uu____7890, c) in
                      FStar_Syntax_Syntax.Tm_arrow uu____7877 in
                    FStar_Syntax_Syntax.mk uu____7876 in
                  uu____7869 FStar_Pervasives_Native.None r1
              | uu____7908 -> typ1 in
            let uu___100_7909 = lb in
            let uu____7910 =
              rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                lb.FStar_Syntax_Syntax.lbtyp in
            {
              FStar_Syntax_Syntax.lbname =
                (uu___100_7909.FStar_Syntax_Syntax.lbname);
              FStar_Syntax_Syntax.lbunivs =
                (uu___100_7909.FStar_Syntax_Syntax.lbunivs);
              FStar_Syntax_Syntax.lbtyp = uu____7910;
              FStar_Syntax_Syntax.lbeff =
                (uu___100_7909.FStar_Syntax_Syntax.lbeff);
              FStar_Syntax_Syntax.lbdef =
                (uu___100_7909.FStar_Syntax_Syntax.lbdef);
              FStar_Syntax_Syntax.lbattrs =
                (uu___100_7909.FStar_Syntax_Syntax.lbattrs);
              FStar_Syntax_Syntax.lbpos =
                (uu___100_7909.FStar_Syntax_Syntax.lbpos)
            } in
          let uu____7913 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.fold_left
                 (fun uu____7964 ->
                    fun lb ->
                      match uu____7964 with
                      | (gen1, lbs1, quals_opt) ->
                          let lbname =
                            FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                          let uu____8006 =
                            let uu____8017 =
                              FStar_TypeChecker_Env.try_lookup_val_decl env1
                                (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            match uu____8017 with
                            | FStar_Pervasives_Native.None ->
                                if lb.FStar_Syntax_Syntax.lbunivs <> []
                                then (false, lb, quals_opt)
                                else (gen1, lb, quals_opt)
                            | FStar_Pervasives_Native.Some
                                ((uvs, tval), quals) ->
                                let quals_opt1 =
                                  check_quals_eq
                                    (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    quals_opt quals in
                                let def =
                                  match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                  with
                                  | FStar_Syntax_Syntax.Tm_unknown ->
                                      lb.FStar_Syntax_Syntax.lbdef
                                  | uu____8102 ->
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           ((lb.FStar_Syntax_Syntax.lbdef),
                                             ((FStar_Util.Inl
                                                 (lb.FStar_Syntax_Syntax.lbtyp)),
                                               FStar_Pervasives_Native.None),
                                             FStar_Pervasives_Native.None))
                                        FStar_Pervasives_Native.None
                                        (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                (if
                                   (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                     ((FStar_List.length
                                         lb.FStar_Syntax_Syntax.lbunivs)
                                        <> (FStar_List.length uvs))
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                       "Inline universes are incoherent with annotation from val declaration")
                                     r
                                 else ();
                                 (let uu____8145 =
                                    FStar_Syntax_Syntax.mk_lb
                                      ((FStar_Util.Inr lbname), uvs,
                                        FStar_Parser_Const.effect_ALL_lid,
                                        tval, def,
                                        (lb.FStar_Syntax_Syntax.lbpos)) in
                                  (false, uu____8145, quals_opt1))) in
                          (match uu____8006 with
                           | (gen2, lb1, quals_opt1) ->
                               (gen2, (lb1 :: lbs1), quals_opt1)))
                 (true, [],
                   (if se.FStar_Syntax_Syntax.sigquals = []
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (se.FStar_Syntax_Syntax.sigquals)))) in
          (match uu____7913 with
           | (should_generalize, lbs', quals_opt) ->
               let quals =
                 match quals_opt with
                 | FStar_Pervasives_Native.None ->
                     [FStar_Syntax_Syntax.Visible_default]
                 | FStar_Pervasives_Native.Some q ->
                     let uu____8239 =
                       FStar_All.pipe_right q
                         (FStar_Util.for_some
                            (fun uu___64_8243 ->
                               match uu___64_8243 with
                               | FStar_Syntax_Syntax.Irreducible -> true
                               | FStar_Syntax_Syntax.Visible_default -> true
                               | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                   -> true
                               | uu____8244 -> false)) in
                     if uu____8239
                     then q
                     else FStar_Syntax_Syntax.Visible_default :: q in
               let lbs'1 = FStar_List.rev lbs' in
               let e =
                 let uu____8254 =
                   let uu____8261 =
                     let uu____8262 =
                       let uu____8275 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_constant
                              FStar_Const.Const_unit)
                           FStar_Pervasives_Native.None r in
                       (((FStar_Pervasives_Native.fst lbs), lbs'1),
                         uu____8275) in
                     FStar_Syntax_Syntax.Tm_let uu____8262 in
                   FStar_Syntax_Syntax.mk uu____8261 in
                 uu____8254 FStar_Pervasives_Native.None r in
               let env0 =
                 let uu___101_8294 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___101_8294.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___101_8294.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___101_8294.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___101_8294.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___101_8294.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___101_8294.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___101_8294.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___101_8294.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___101_8294.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___101_8294.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___101_8294.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize = should_generalize;
                   FStar_TypeChecker_Env.letrecs =
                     (uu___101_8294.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = true;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___101_8294.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___101_8294.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___101_8294.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___101_8294.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___101_8294.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___101_8294.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___101_8294.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___101_8294.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___101_8294.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___101_8294.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___101_8294.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___101_8294.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___101_8294.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___101_8294.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___101_8294.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___101_8294.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___101_8294.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___101_8294.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___101_8294.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___101_8294.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___101_8294.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___101_8294.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___101_8294.FStar_TypeChecker_Env.dep_graph)
                 } in
               let e1 =
                 let uu____8296 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env0) in
                 if uu____8296
                 then
                   let drop_lbtyp e_lax =
                     let uu____8303 =
                       let uu____8304 = FStar_Syntax_Subst.compress e_lax in
                       uu____8304.FStar_Syntax_Syntax.n in
                     match uu____8303 with
                     | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) ->
                         let lb_unannotated =
                           let uu____8322 =
                             let uu____8323 = FStar_Syntax_Subst.compress e in
                             uu____8323.FStar_Syntax_Syntax.n in
                           match uu____8322 with
                           | FStar_Syntax_Syntax.Tm_let
                               ((uu____8326, lb1::[]), uu____8328) ->
                               let uu____8341 =
                                 let uu____8342 =
                                   FStar_Syntax_Subst.compress
                                     lb1.FStar_Syntax_Syntax.lbtyp in
                                 uu____8342.FStar_Syntax_Syntax.n in
                               uu____8341 = FStar_Syntax_Syntax.Tm_unknown
                           | uu____8345 ->
                               failwith
                                 "Impossible: first phase lb and second phase lb differ in structure!" in
                         if lb_unannotated
                         then
                           let uu___102_8346 = e_lax in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false,
                                     [(let uu___103_8358 = lb in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           FStar_Syntax_Syntax.tun;
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbdef);
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___103_8358.FStar_Syntax_Syntax.lbpos)
                                       })]), e2));
                             FStar_Syntax_Syntax.pos =
                               (uu___102_8346.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___102_8346.FStar_Syntax_Syntax.vars)
                           }
                         else e_lax
                     | uu____8360 -> e_lax in
                   let e1 =
                     let uu____8362 =
                       let uu____8363 =
                         let uu____8364 =
                           FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                             (let uu___104_8373 = env0 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___104_8373.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___104_8373.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___104_8373.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___104_8373.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___104_8373.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___104_8373.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___104_8373.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___104_8373.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___104_8373.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___104_8373.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___104_8373.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___104_8373.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___104_8373.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___104_8373.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___104_8373.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___104_8373.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___104_8373.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___104_8373.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___104_8373.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___104_8373.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___104_8373.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___104_8373.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___104_8373.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___104_8373.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___104_8373.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___104_8373.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___104_8373.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___104_8373.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___104_8373.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___104_8373.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___104_8373.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___104_8373.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___104_8373.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___104_8373.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___104_8373.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___104_8373.FStar_TypeChecker_Env.dep_graph)
                              }) e in
                         FStar_All.pipe_right uu____8364
                           (fun uu____8384 ->
                              match uu____8384 with
                              | (e1, uu____8392, uu____8393) -> e1) in
                       FStar_All.pipe_right uu____8363
                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                            env0) in
                     FStar_All.pipe_right uu____8362 drop_lbtyp in
                   ((let uu____8395 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____8395
                     then
                       let uu____8396 = FStar_Syntax_Print.term_to_string e1 in
                       FStar_Util.print1 "Let binding after phase 1: %s\n"
                         uu____8396
                     else ());
                    e1)
                 else e in
               let uu____8399 =
                 let uu____8410 =
                   FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1 in
                 match uu____8410 with
                 | ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                        (lbs1, e2);
                      FStar_Syntax_Syntax.pos = uu____8429;
                      FStar_Syntax_Syntax.vars = uu____8430;_},
                    uu____8431, g) when FStar_TypeChecker_Rel.is_trivial g ->
                     let lbs2 =
                       let uu____8460 =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs1)
                           (FStar_List.map rename_parameters) in
                       ((FStar_Pervasives_Native.fst lbs1), uu____8460) in
                     let quals1 =
                       match e2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_meta
                           (uu____8478, FStar_Syntax_Syntax.Meta_desugared
                            (FStar_Syntax_Syntax.Masked_effect))
                           -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                       | uu____8483 -> quals in
                     ((let uu___105_8491 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___105_8491.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___105_8491.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___105_8491.FStar_Syntax_Syntax.sigattrs)
                       }), lbs2)
                 | uu____8500 ->
                     failwith
                       "impossible (typechecking should preserve Tm_let)" in
               (match uu____8399 with
                | (se1, lbs1) ->
                    (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                       (FStar_List.iter
                          (fun lb ->
                             let fv =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                             FStar_TypeChecker_Env.insert_fv_info env1 fv
                               lb.FStar_Syntax_Syntax.lbtyp));
                     (let uu____8549 = log env1 in
                      if uu____8549
                      then
                        let uu____8550 =
                          let uu____8551 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs1)
                              (FStar_List.map
                                 (fun lb ->
                                    let should_log =
                                      let uu____8566 =
                                        let uu____8575 =
                                          let uu____8576 =
                                            let uu____8579 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            uu____8579.FStar_Syntax_Syntax.fv_name in
                                          uu____8576.FStar_Syntax_Syntax.v in
                                        FStar_TypeChecker_Env.try_lookup_val_decl
                                          env1 uu____8575 in
                                      match uu____8566 with
                                      | FStar_Pervasives_Native.None -> true
                                      | uu____8586 -> false in
                                    if should_log
                                    then
                                      let uu____8595 =
                                        FStar_Syntax_Print.lbname_to_string
                                          lb.FStar_Syntax_Syntax.lbname in
                                      let uu____8596 =
                                        FStar_Syntax_Print.term_to_string
                                          lb.FStar_Syntax_Syntax.lbtyp in
                                      FStar_Util.format2 "let %s : %s"
                                        uu____8595 uu____8596
                                    else "")) in
                          FStar_All.pipe_right uu____8551
                            (FStar_String.concat "\n") in
                        FStar_Util.print1 "%s\n" uu____8550
                      else ());
                     ([se1], []))))
let (for_export :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list, FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun hidden ->
    fun se ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___65_8648 ->
                match uu___65_8648 with
                | FStar_Syntax_Syntax.Abstract -> true
                | uu____8649 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l, uu____8657) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____8663 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____8672 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_splice uu____8677 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____8692 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____8717 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____8741) ->
          let uu____8750 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____8750
          then
            let for_export_bundle se1 uu____8785 =
              match uu____8785 with
              | (out, hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l, us, bs, t, uu____8824, uu____8825) ->
                       let dec =
                         let uu___106_8835 = se1 in
                         let uu____8836 =
                           let uu____8837 =
                             let uu____8844 =
                               let uu____8847 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____8847 in
                             (l, us, uu____8844) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____8837 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____8836;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___106_8835.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___106_8835.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___106_8835.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l, us, t, uu____8859, uu____8860, uu____8861) ->
                       let dec =
                         let uu___107_8867 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___107_8867.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___107_8867.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___107_8867.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____8872 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____8894, uu____8895, uu____8896)
          ->
          let uu____8897 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____8897 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
          let uu____8918 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____8918
          then
            ([(let uu___108_8934 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___108_8934.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___108_8934.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___108_8934.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____8936 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___66_8940 ->
                       match uu___66_8940 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | FStar_Syntax_Syntax.Projector uu____8941 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____8946 -> true
                       | uu____8947 -> false)) in
             if uu____8936 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____8965 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____8970 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8975 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8980 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____8985 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____9003) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____9020 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____9020
          then ([], hidden)
          else
            (let dec =
               let uu____9037 = FStar_Ident.range_of_lid lid in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = uu____9037;
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
          let uu____9052 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____9052
          then
            let uu____9061 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb ->
                      let uu___109_9074 = se in
                      let uu____9075 =
                        let uu____9076 =
                          let uu____9083 =
                            let uu____9084 =
                              let uu____9087 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____9087.FStar_Syntax_Syntax.fv_name in
                            uu____9084.FStar_Syntax_Syntax.v in
                          (uu____9083, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____9076 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____9075;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___109_9074.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___109_9074.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___109_9074.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____9061, hidden)
          else ([se], hidden)
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9111 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____9128 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____9143) -> z3_reset_options env
      | FStar_Syntax_Syntax.Sig_pragma uu____9146 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9147 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2 ->
                  fun a ->
                    let uu____9157 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a
                        (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____9157) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____9158, uu____9159, uu____9160) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___67_9164 ->
                  match uu___67_9164 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____9165 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____9166, uu____9167) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___67_9175 ->
                  match uu___67_9175 with
                  | FStar_Syntax_Syntax.OnlyName -> true
                  | uu____9176 -> false))
          -> env
      | uu____9177 -> FStar_TypeChecker_Env.push_sigelt env se
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_Syntax_Syntax.sigelt Prims.list, FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____9245 se =
        match uu____9245 with
        | (ses1, exports, env1, hidden) ->
            ((let uu____9298 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____9298
              then
                let uu____9299 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____9299
              else ());
             (let uu____9301 = tc_decl env1 se in
              match uu____9301 with
              | (ses', ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1 ->
                            (let uu____9351 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____9351
                             then
                               let uu____9352 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____9352
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1 ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  (FStar_TypeChecker_Env.promote_id_info env1
                     (fun t ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                          FStar_TypeChecker_Normalize.CheckNoUvars;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                          FStar_TypeChecker_Normalize.CompressUvars;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Zeta;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Iota;
                          FStar_TypeChecker_Normalize.NoFullNorm] env1 t);
                   (let env2 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env2 -> fun se1 -> add_sigelt_to_env env2 se1)
                           env1) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____9375 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____9375
                     then
                       let uu____9376 =
                         FStar_List.fold_left
                           (fun s ->
                              fun se1 ->
                                let uu____9382 =
                                  let uu____9383 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____9383 "\n" in
                                Prims.strcat s uu____9382) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____9376
                     else ());
                    FStar_List.iter
                      (fun se1 ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____9388 =
                       let uu____9397 =
                         FStar_Options.use_extracted_interfaces () in
                       if uu____9397
                       then ([], [])
                       else
                         (let accum_exports_hidden uu____9436 se1 =
                            match uu____9436 with
                            | (exports1, hidden1) ->
                                let uu____9464 = for_export hidden1 se1 in
                                (match uu____9464 with
                                 | (se_exported, hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2)) in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1) in
                     match uu____9388 with
                     | (exports1, hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s ->
                                let uu___110_9543 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___110_9543.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___110_9543.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___110_9543.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___110_9543.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____9625 = acc in
        match uu____9625 with
        | (uu____9660, uu____9661, env1, uu____9663) ->
            let uu____9676 =
              FStar_Util.record_time
                (fun uu____9722 -> process_one_decl acc se) in
            (match uu____9676 with
             | (r, ms_elapsed) ->
                 ((let uu____9786 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____9786
                   then
                     let uu____9787 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____9788 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____9787 uu____9788
                   else ());
                  r)) in
      let uu____9790 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____9790 with
      | (ses1, exports, env1, uu____9838) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env ->
    fun modul ->
      fun exports ->
        let env1 =
          let uu___111_9875 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___111_9875.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___111_9875.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___111_9875.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___111_9875.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___111_9875.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___111_9875.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___111_9875.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___111_9875.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___111_9875.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___111_9875.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___111_9875.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___111_9875.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___111_9875.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___111_9875.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___111_9875.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___111_9875.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___111_9875.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___111_9875.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___111_9875.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___111_9875.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___111_9875.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___111_9875.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___111_9875.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___111_9875.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___111_9875.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___111_9875.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.proof_ns =
              (uu___111_9875.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___111_9875.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___111_9875.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___111_9875.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___111_9875.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___111_9875.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___111_9875.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___111_9875.FStar_TypeChecker_Env.dep_graph)
          } in
        let check_term lid univs1 t =
          let uu____9892 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____9892 with
          | (univs2, t1) ->
              ((let uu____9900 =
                  let uu____9901 =
                    let uu____9906 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____9906 in
                  FStar_All.pipe_left uu____9901
                    (FStar_Options.Other "Exports") in
                if uu____9900
                then
                  let uu____9907 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____9908 =
                    let uu____9909 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____9909
                      (FStar_String.concat ", ") in
                  let uu____9918 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____9907 uu____9908 uu____9918
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____9921 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____9921 (fun a240 -> ()))) in
        let check_term1 lid univs1 t =
          (let uu____9947 =
             let uu____9948 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____9949 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____9948 uu____9949 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____9947);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9958) ->
              let uu____9967 =
                let uu____9968 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____9968 in
              if uu____9967
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l, univs1, binders, typ, uu____9978, uu____9979) ->
              let t =
                let uu____9991 =
                  let uu____9998 =
                    let uu____9999 =
                      let uu____10012 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____10012) in
                    FStar_Syntax_Syntax.Tm_arrow uu____9999 in
                  FStar_Syntax_Syntax.mk uu____9998 in
                uu____9991 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l, univs1, t, uu____10019, uu____10020, uu____10021) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) ->
              let uu____10029 =
                let uu____10030 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____10030 in
              if uu____10029 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____10034, lbs), uu____10036) ->
              let uu____10051 =
                let uu____10052 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____10052 in
              if uu____10051
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l, univs1, binders, comp, flags1) ->
              let uu____10071 =
                let uu____10072 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____10072 in
              if uu____10071
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____10079 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____10080 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____10087 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10088 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____10089 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____10090 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____10097 -> () in
        let uu____10098 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____10098 then () else FStar_List.iter check_sigelt exports
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en ->
    fun m ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption in
      let filter_out_abstract =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) in
      let abstract_inductive_tycons = FStar_Util.mk_ref [] in
      let abstract_inductive_datacons = FStar_Util.mk_ref [] in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l, uu____10193) -> true
             | uu____10194 -> false) quals in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____10221 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs', c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____10252 ->
                   let uu____10253 =
                     let uu____10260 =
                       let uu____10261 =
                         let uu____10274 = FStar_Syntax_Syntax.mk_Total t in
                         (bs, uu____10274) in
                       FStar_Syntax_Syntax.Tm_arrow uu____10261 in
                     FStar_Syntax_Syntax.mk uu____10260 in
                   uu____10253 FStar_Pervasives_Native.None r) in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, uvs, bs, t, uu____10282, uu____10283) ->
            let s1 =
              let uu___112_10293 = s in
              let uu____10294 =
                let uu____10295 =
                  let uu____10302 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng in
                  (lid, uvs, uu____10302) in
                FStar_Syntax_Syntax.Sig_declare_typ uu____10295 in
              let uu____10303 =
                let uu____10306 =
                  let uu____10309 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals in
                  FStar_Syntax_Syntax.New :: uu____10309 in
                FStar_Syntax_Syntax.Assumption :: uu____10306 in
              {
                FStar_Syntax_Syntax.sigel = uu____10294;
                FStar_Syntax_Syntax.sigrng =
                  (uu___112_10293.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____10303;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___112_10293.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___112_10293.FStar_Syntax_Syntax.sigattrs)
              } in
            [s1]
        | uu____10312 -> failwith "Impossible!" in
      let val_of_lb s lid uu____10336 lbdef =
        match uu____10336 with
        | (uvs, t) ->
            let attrs =
              let uu____10347 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef in
              if uu____10347
              then
                let uu____10350 =
                  let uu____10351 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_right uu____10351
                    FStar_Syntax_Syntax.fv_to_tm in
                uu____10350 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs in
            let uu___113_10353 = s in
            let uu____10354 =
              let uu____10357 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals in
              FStar_Syntax_Syntax.Assumption :: uu____10357 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___113_10353.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____10354;
              FStar_Syntax_Syntax.sigmeta =
                (uu___113_10353.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            } in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____10373 -> failwith "Impossible!" in
        let c_opt =
          let uu____10377 = FStar_Syntax_Util.is_unit t in
          if uu____10377
          then
            let uu____10380 = FStar_Syntax_Syntax.mk_Total t in
            FStar_Pervasives_Native.Some uu____10380
          else
            (let uu____10382 =
               let uu____10383 = FStar_Syntax_Subst.compress t in
               uu____10383.FStar_Syntax_Syntax.n in
             match uu____10382 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____10388, c) ->
                 FStar_Pervasives_Native.Some c
             | uu____10408 -> FStar_Pervasives_Native.None) in
        (c_opt = FStar_Pervasives_Native.None) ||
          (let c = FStar_All.pipe_right c_opt FStar_Util.must in
           let uu____10417 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
           if uu____10417
           then
             let uu____10418 =
               let uu____10419 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_result in
               FStar_All.pipe_right uu____10419 FStar_Syntax_Util.is_unit in
             Prims.op_Negation uu____10418
           else
             (let uu____10427 = comp_effect_name1 c in
              FStar_TypeChecker_Env.is_reifiable_effect en uu____10427)) in
      let extract_sigelt s =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____10438 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_datacon uu____10457 ->
            failwith "Impossible! extract_interface: bare data constructor"
        | FStar_Syntax_Syntax.Sig_splice uu____10474 ->
            failwith
              "Impossible! extract_interface: trying to extract splice"
        | FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) ->
            if is_abstract s.FStar_Syntax_Syntax.sigquals
            then
              FStar_All.pipe_right sigelts
                (FStar_List.fold_left
                   (fun sigelts1 ->
                      fun s1 ->
                        match s1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (lid, uu____10518, uu____10519, uu____10520,
                             uu____10521, uu____10522)
                            ->
                            ((let uu____10532 =
                                let uu____10535 =
                                  FStar_ST.op_Bang abstract_inductive_tycons in
                                lid :: uu____10535 in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_tycons uu____10532);
                             (let uu____10744 = vals_of_abstract_inductive s1 in
                              FStar_List.append uu____10744 sigelts1))
                        | FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____10748, uu____10749, uu____10750,
                             uu____10751, uu____10752)
                            ->
                            ((let uu____10758 =
                                let uu____10761 =
                                  FStar_ST.op_Bang
                                    abstract_inductive_datacons in
                                lid :: uu____10761 in
                              FStar_ST.op_Colon_Equals
                                abstract_inductive_datacons uu____10758);
                             sigelts1)
                        | uu____10970 ->
                            failwith
                              "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                   [])
            else [s]
        | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
            let uu____10977 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals in
            if uu____10977
            then []
            else
              if is_assume s.FStar_Syntax_Syntax.sigquals
              then
                (let uu____10983 =
                   let uu___114_10984 = s in
                   let uu____10985 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___114_10984.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___114_10984.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____10985;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___114_10984.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___114_10984.FStar_Syntax_Syntax.sigattrs)
                   } in
                 [uu____10983])
              else []
        | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
            let uu____10995 =
              is_projector_or_discriminator_of_an_abstract_inductive
                s.FStar_Syntax_Syntax.sigquals in
            if uu____10995
            then []
            else
              (let uu____10999 = lbs in
               match uu____10999 with
               | (flbs, slbs) ->
                   let typs_and_defs =
                     FStar_All.pipe_right slbs
                       (FStar_List.map
                          (fun lb ->
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp),
                               (lb.FStar_Syntax_Syntax.lbdef)))) in
                   let is_lemma1 =
                     FStar_List.existsML
                       (fun uu____11074 ->
                          match uu____11074 with
                          | (uu____11085, t, uu____11087) ->
                              FStar_All.pipe_right t
                                FStar_Syntax_Util.is_lemma) typs_and_defs in
                   let vals =
                     FStar_List.map2
                       (fun lid ->
                          fun uu____11111 ->
                            match uu____11111 with
                            | (u, t, d) -> val_of_lb s lid (u, t) d) lids
                       typs_and_defs in
                   if
                     ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                        (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                       || is_lemma1
                   then vals
                   else
                     (let should_keep_defs =
                        FStar_List.existsML
                          (fun uu____11139 ->
                             match uu____11139 with
                             | (uu____11150, t, uu____11152) ->
                                 FStar_All.pipe_right t should_keep_lbdef)
                          typs_and_defs in
                      if should_keep_defs then [s] else vals))
        | FStar_Syntax_Syntax.Sig_main t ->
            failwith
              "Did not anticipate main would arise when extracting interfaces!"
        | FStar_Syntax_Syntax.Sig_assume (lid, uu____11168, uu____11169) ->
            let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid in
            if is_haseq
            then
              let is_haseq_of_abstract_inductive =
                let uu____11174 = FStar_ST.op_Bang abstract_inductive_tycons in
                FStar_List.existsML
                  (fun l ->
                     let uu____11283 =
                       FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l in
                     FStar_Ident.lid_equals lid uu____11283) uu____11174 in
              (if is_haseq_of_abstract_inductive
               then
                 let uu____11286 =
                   let uu___115_11287 = s in
                   let uu____11288 =
                     filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___115_11287.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___115_11287.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals = uu____11288;
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___115_11287.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___115_11287.FStar_Syntax_Syntax.sigattrs)
                   } in
                 [uu____11286]
               else [])
            else
              (let uu____11293 =
                 let uu___116_11294 = s in
                 let uu____11295 =
                   filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___116_11294.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___116_11294.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals = uu____11295;
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___116_11294.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___116_11294.FStar_Syntax_Syntax.sigattrs)
                 } in
               [uu____11293])
        | FStar_Syntax_Syntax.Sig_new_effect uu____11298 -> [s]
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11299 -> [s]
        | FStar_Syntax_Syntax.Sig_sub_effect uu____11300 -> [s]
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11301 -> [s]
        | FStar_Syntax_Syntax.Sig_pragma uu____11314 -> [s] in
      let uu___117_11315 = m in
      let uu____11316 =
        let uu____11317 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt) in
        FStar_All.pipe_right uu____11317 FStar_List.flatten in
      {
        FStar_Syntax_Syntax.name = (uu___117_11315.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11316;
        FStar_Syntax_Syntax.exports =
          (uu___117_11315.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      (let uu____11345 = FStar_Syntax_DsEnv.pop () in
       FStar_All.pipe_right uu____11345 (fun a241 -> ()));
      (let en = FStar_TypeChecker_Env.pop env msg in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
       en)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let dsenv1 = FStar_Syntax_DsEnv.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___118_11360 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___118_11360.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___118_11360.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___118_11360.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___118_11360.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___118_11360.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___118_11360.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___118_11360.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___118_11360.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___118_11360.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___118_11360.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___118_11360.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___118_11360.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___118_11360.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___118_11360.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___118_11360.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___118_11360.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___118_11360.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___118_11360.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___118_11360.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___118_11360.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___118_11360.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___118_11360.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___118_11360.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___118_11360.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___118_11360.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___118_11360.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___118_11360.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___118_11360.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___118_11360.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___118_11360.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___118_11360.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___118_11360.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___118_11360.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___118_11360.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___118_11360.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv1;
        FStar_TypeChecker_Env.dep_graph =
          (uu___118_11360.FStar_TypeChecker_Env.dep_graph)
      }
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul, FStar_Syntax_Syntax.sigelt Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun modul ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____11385 = FStar_Options.debug_any () in
       if uu____11385
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let env1 =
         let uu___119_11390 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___119_11390.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___119_11390.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___119_11390.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___119_11390.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___119_11390.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___119_11390.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___119_11390.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___119_11390.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___119_11390.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___119_11390.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___119_11390.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___119_11390.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___119_11390.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___119_11390.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___119_11390.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___119_11390.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___119_11390.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___119_11390.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___119_11390.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___119_11390.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___119_11390.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___119_11390.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___119_11390.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___119_11390.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___119_11390.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___119_11390.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___119_11390.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___119_11390.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___119_11390.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___119_11390.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___119_11390.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___119_11390.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___119_11390.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___119_11390.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___119_11390.FStar_TypeChecker_Env.dep_graph)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____11392 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____11392 with
       | (ses, exports, env3) ->
           ((let uu___120_11425 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___120_11425.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___120_11425.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___120_11425.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul, FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun modul ->
      fun decls ->
        let uu____11453 = tc_decls env decls in
        match uu____11453 with
        | (ses, exports, env1) ->
            let modul1 =
              let uu___121_11484 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___121_11484.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___121_11484.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___121_11484.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,
        FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env0 ->
    fun m ->
      let msg =
        Prims.strcat "Internals for "
          (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let env01 = push_context env0 msg in
      let uu____11541 = tc_partial_modul env01 m in
      match uu____11541 with
      | (modul, non_private_decls, env) ->
          finish_partial_modul false env modul non_private_decls
and (finish_partial_modul :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.modul,
            FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,
            FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun loading_from_cache ->
    fun en ->
      fun m ->
        fun exports ->
          let uu____11579 =
            ((Prims.op_Negation loading_from_cache) &&
               (FStar_Options.use_extracted_interfaces ()))
              && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface) in
          if uu____11579
          then
            let modul_iface = extract_interface en m in
            ((let uu____11590 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                  FStar_Options.Low in
              if uu____11590
              then
                let uu____11591 =
                  let uu____11592 =
                    FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                  if uu____11592 then "" else " (in lax mode) " in
                let uu____11594 =
                  let uu____11595 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                  if uu____11595
                  then
                    let uu____11596 =
                      let uu____11597 = FStar_Syntax_Print.modul_to_string m in
                      Prims.strcat uu____11597 "\n" in
                    Prims.strcat "\nfrom: " uu____11596
                  else "" in
                let uu____11599 =
                  let uu____11600 =
                    FStar_Options.dump_module
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                  if uu____11600
                  then
                    let uu____11601 =
                      let uu____11602 =
                        FStar_Syntax_Print.modul_to_string modul_iface in
                      Prims.strcat uu____11602 "\n" in
                    Prims.strcat "\nto: " uu____11601
                  else "" in
                FStar_Util.print4
                  "Extracting and type checking module %s interface%s%s%s\n"
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____11591
                  uu____11594 uu____11599
              else ());
             (let en0 =
                let en0 =
                  pop_context en
                    (Prims.strcat "Ending modul "
                       (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
                let en01 =
                  let uu___122_11608 = en0 in
                  let uu____11609 =
                    let uu____11622 =
                      FStar_All.pipe_right
                        en.FStar_TypeChecker_Env.qtbl_name_and_index
                        FStar_Pervasives_Native.fst in
                    (uu____11622, FStar_Pervasives_Native.None) in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___122_11608.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___122_11608.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___122_11608.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___122_11608.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___122_11608.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___122_11608.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___122_11608.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___122_11608.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___122_11608.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___122_11608.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___122_11608.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___122_11608.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___122_11608.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___122_11608.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___122_11608.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___122_11608.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___122_11608.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___122_11608.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___122_11608.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___122_11608.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___122_11608.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___122_11608.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___122_11608.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___122_11608.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___122_11608.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___122_11608.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___122_11608.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index = uu____11609;
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___122_11608.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___122_11608.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___122_11608.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___122_11608.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___122_11608.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___122_11608.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___122_11608.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___122_11608.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___122_11608.FStar_TypeChecker_Env.dep_graph)
                  } in
                let uu____11659 =
                  let uu____11660 = FStar_Options.interactive () in
                  Prims.op_Negation uu____11660 in
                if uu____11659
                then
                  ((let uu____11662 =
                      FStar_Options.restore_cmd_line_options true in
                    FStar_All.pipe_right uu____11662 (fun a242 -> ()));
                   z3_reset_options en01)
                else en01 in
              let uu____11664 = tc_modul en0 modul_iface in
              match uu____11664 with
              | (modul_iface1, must_be_none, env) ->
                  if must_be_none <> FStar_Pervasives_Native.None
                  then
                    failwith
                      "Impossible! finish_partial_module: expected the second component to be None"
                  else
                    (((let uu___123_11710 = m in
                       {
                         FStar_Syntax_Syntax.name =
                           (uu___123_11710.FStar_Syntax_Syntax.name);
                         FStar_Syntax_Syntax.declarations =
                           (uu___123_11710.FStar_Syntax_Syntax.declarations);
                         FStar_Syntax_Syntax.exports =
                           (modul_iface1.FStar_Syntax_Syntax.exports);
                         FStar_Syntax_Syntax.is_interface =
                           (uu___123_11710.FStar_Syntax_Syntax.is_interface)
                       })), (FStar_Pervasives_Native.Some modul_iface1), env)))
          else
            (let modul =
               let uu____11713 = FStar_Options.use_extracted_interfaces () in
               if uu____11713
               then
                 let uu___124_11714 = m in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___124_11714.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___124_11714.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports =
                     (m.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___124_11714.FStar_Syntax_Syntax.is_interface)
                 }
               else
                 (let uu___125_11716 = m in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___125_11716.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations =
                      (uu___125_11716.FStar_Syntax_Syntax.declarations);
                    FStar_Syntax_Syntax.exports = exports;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___125_11716.FStar_Syntax_Syntax.is_interface)
                  }) in
             let env = FStar_TypeChecker_Env.finish_module en modul in
             (let uu____11719 =
                FStar_All.pipe_right
                  env.FStar_TypeChecker_Env.qtbl_name_and_index
                  FStar_Pervasives_Native.fst in
              FStar_All.pipe_right uu____11719 FStar_Util.smap_clear);
             (let uu____11747 =
                ((let uu____11750 = FStar_Options.lax () in
                  Prims.op_Negation uu____11750) &&
                   (let uu____11752 =
                      FStar_Options.use_extracted_interfaces () in
                    Prims.op_Negation uu____11752))
                  && (Prims.op_Negation loading_from_cache) in
              if uu____11747 then check_exports env modul exports else ());
             (let uu____11755 =
                pop_context env
                  (Prims.strcat "Ending modul "
                     (modul.FStar_Syntax_Syntax.name).FStar_Ident.str) in
              FStar_All.pipe_right uu____11755 (fun a243 -> ()));
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
               env modul;
             (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
               ();
             (let uu____11759 =
                let uu____11760 = FStar_Options.interactive () in
                Prims.op_Negation uu____11760 in
              if uu____11759
              then
                let uu____11761 = FStar_Options.restore_cmd_line_options true in
                FStar_All.pipe_right uu____11761 (fun a244 -> ())
              else ());
             (modul, FStar_Pervasives_Native.None, env))
let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name in
      let env1 =
        let uu____11777 =
          let uu____11778 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.strcat "Internals for " uu____11778 in
        push_context env uu____11777 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____11797 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____11808 =
        finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports in
      match uu____11808 with | (uu____11817, uu____11818, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,
        FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun m ->
      (let uu____11843 = FStar_Options.debug_any () in
       if uu____11843
       then
         let uu____11844 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____11844
       else ());
      (let env1 =
         let uu___126_11848 = env in
         let uu____11849 =
           let uu____11850 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____11850 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___126_11848.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___126_11848.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___126_11848.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___126_11848.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___126_11848.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___126_11848.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___126_11848.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___126_11848.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___126_11848.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___126_11848.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___126_11848.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___126_11848.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___126_11848.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___126_11848.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___126_11848.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___126_11848.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___126_11848.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___126_11848.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____11849;
           FStar_TypeChecker_Env.lax_universes =
             (uu___126_11848.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___126_11848.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___126_11848.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___126_11848.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___126_11848.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___126_11848.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___126_11848.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___126_11848.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___126_11848.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___126_11848.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___126_11848.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___126_11848.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___126_11848.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___126_11848.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___126_11848.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___126_11848.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___126_11848.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___126_11848.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____11851 = tc_modul env1 m in
       match uu____11851 with
       | (m1, m_iface_opt, env2) ->
           ((let uu____11876 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____11876
             then
               let uu____11877 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "Module after type checking:\n%s\n"
                 uu____11877
             else ());
            (let uu____11880 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____11880
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____11919 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____11919 with
                       | (univnames1, e) ->
                           let uu___127_11926 = lb in
                           let uu____11927 =
                             let uu____11930 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____11930 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___127_11926.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_11926.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___127_11926.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_11926.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____11927;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_11926.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_11926.FStar_Syntax_Syntax.lbpos)
                           } in
                     let uu___128_11931 = se in
                     let uu____11932 =
                       let uu____11933 =
                         let uu____11940 =
                           let uu____11947 = FStar_List.map update lbs in
                           (b, uu____11947) in
                         (uu____11940, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____11933 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____11932;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___128_11931.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___128_11931.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___128_11931.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___128_11931.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____11960 -> se in
               let normalized_module =
                 let uu___129_11962 = m1 in
                 let uu____11963 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___129_11962.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____11963;
                   FStar_Syntax_Syntax.exports =
                     (uu___129_11962.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___129_11962.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____11964 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____11964
             else ());
            (m1, m_iface_opt, env2)))