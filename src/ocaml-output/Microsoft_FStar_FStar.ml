
let process_args = (fun _58_1 -> (match (_58_1) with
| () -> begin
(let file_list = (Support.Microsoft.FStar.Util.mk_ref [])
in (let res = (Support.Microsoft.FStar.Getopt.parse_cmdline (Microsoft_FStar_Options.specs ()) (fun i -> (Support.ST.op_Colon_Equals file_list (Support.List.append (! (file_list)) ((i)::[])))))
in (let _58_8 = (match (res) with
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(Support.Prims.ignore (Microsoft_FStar_Options.set_fstar_home ()))
end
| _ -> begin
()
end)
in (res, (! (file_list))))))
end))

let cleanup = (fun _58_10 -> (match (_58_10) with
| () -> begin
(Support.Microsoft.FStar.Util.kill_all ())
end))

let has_prims_cache = (fun l -> (Support.List.mem "Prims.cache" l))

let tc_prims = (fun _58_12 -> (match (_58_12) with
| () -> begin
(let solver = if (! (Microsoft_FStar_Options.verify)) then begin
Microsoft_FStar_ToSMT_Encode.solver
end else begin
Microsoft_FStar_ToSMT_Encode.dummy
end
in (let env = (Microsoft_FStar_Tc_Env.initial_env solver Microsoft_FStar_Absyn_Const.prims_lid)
in (let _58_15 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.init env)
in (let p = (Microsoft_FStar_Options.prims ())
in (let _58_20 = (Microsoft_FStar_Parser_Driver.parse_file (Microsoft_FStar_Parser_DesugarEnv.empty_env ()) p)
in (match (_58_20) with
| (dsenv, prims_mod) -> begin
(let _58_23 = (Microsoft_FStar_Tc_Tc.check_module env (Support.List.hd prims_mod))
in (match (_58_23) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let report_errors = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(Microsoft_FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(let _58_29 = (Support.Microsoft.FStar.Util.fprint1 "Error: %s errors were reported (see above)\n" (Support.Microsoft.FStar.Util.string_of_int errs))
in (exit (1)))
end))

let tc_one_file = (fun dsenv env fn -> (let _58_36 = (Microsoft_FStar_Parser_Driver.parse_file dsenv fn)
in (match (_58_36) with
| (dsenv, fmods) -> begin
(let _58_46 = ((Support.List.fold_left (fun _58_39 m -> (match (_58_39) with
| (env, all_mods) -> begin
(let _58_43 = (Microsoft_FStar_Tc_Tc.check_module env m)
in (match (_58_43) with
| (ms, env) -> begin
(env, ms)
end))
end)) (env, [])) fmods)
in (match (_58_46) with
| (env, all_mods) -> begin
(dsenv, env, (Support.List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun curmod dsenv env frag -> (Support.Prims.try_with (fun _58_52 -> (match (_58_52) with
| () -> begin
(match ((Microsoft_FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| Support.Microsoft.FStar.Util.Inl ((dsenv, modul)) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _58_79 = (Microsoft_FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_58_79) with
| (modul, npds, env) -> begin
Some ((Some ((modul, npds)), dsenv, env))
end)))
end
| Support.Microsoft.FStar.Util.Inr ((dsenv, decls)) -> begin
(match (curmod) with
| None -> begin
(failwith "Fragment without an enclosing module")
end
| Some ((modul, npds)) -> begin
(let _58_92 = (Microsoft_FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_58_92) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (Support.List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _58_51 -> (match (_58_51) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _58_58 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| Microsoft_FStar_Absyn_Syntax.Err (msg) -> begin
(let _58_62 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, Microsoft_FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(raise (e))
end))))

type input_chunks =
| Push of string
| Pop of string
| Code of (string * (string * string))

type stack_elt =
((Microsoft_FStar_Absyn_Syntax.modul * Microsoft_FStar_Absyn_Syntax.sigelt list) option * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Tc_Env.env)

type stack =
stack_elt list

let interactive_mode = (fun dsenv env -> (let should_log = ((! (Microsoft_FStar_Options.debug)) <> [])
in (let log = if should_log then begin
(let transcript = (Support.Microsoft.FStar.Util.open_file_for_writing "transcript")
in (fun line -> (let _58_104 = (Support.Microsoft.FStar.Util.append_to_file transcript line)
in (Support.Microsoft.FStar.Util.flush_file transcript))))
end else begin
(fun line -> ())
end
in (let _58_110 = if (Support.Option.isSome (! (Microsoft_FStar_Options.codegen))) then begin
(let _58_108 = (Support.Microsoft.FStar.Util.print_string "Code-generation is not supported in interactive mode")
in (exit (1)))
end
in (let chunk = (Support.Microsoft.FStar.Util.new_string_builder ())
in (let stdin = (Support.Microsoft.FStar.Util.open_stdin ())
in (let rec fill_chunk = (fun _58_115 -> (match (_58_115) with
| () -> begin
(let line = (match ((Support.Microsoft.FStar.Util.read_line stdin)) with
| None -> begin
(exit (0))
end
| Some (l) -> begin
l
end)
in (let _58_120 = (log line)
in (let l = (Support.Microsoft.FStar.Util.trim_string line)
in if (Support.Microsoft.FStar.Util.starts_with l "#end") then begin
(let responses = (match ((Support.Microsoft.FStar.Util.split l " ")) with
| _::ok::fail::[] -> begin
(ok, fail)
end
| _ -> begin
("ok", "fail")
end)
in (let str = (Support.Microsoft.FStar.Util.string_of_string_builder chunk)
in (let _58_132 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Code ((str, responses)))))
end else begin
if (Support.Microsoft.FStar.Util.starts_with l "#pop") then begin
(let _58_134 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Pop (l))
end else begin
if (Support.Microsoft.FStar.Util.starts_with l "#push") then begin
(let _58_136 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(exit (0))
end else begin
(let _58_138 = (Support.Microsoft.FStar.Util.string_builder_append chunk line)
in (let _58_140 = (Support.Microsoft.FStar.Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end
end
end
end)))
end))
in (let rec go = (fun stack curmod dsenv env -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _58_149 = ((Support.Prims.ignore) (Microsoft_FStar_Tc_Env.pop env msg))
in (let _58_151 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _58_153 = ((Support.Prims.ignore) (Microsoft_FStar_Options.reset_options ()))
in (let _58_164 = (match (stack) with
| [] -> begin
(failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_58_164) with
| ((curmod, dsenv, env), stack) -> begin
(go stack curmod dsenv env)
end)))))
end
| Push (msg) -> begin
(let stack = ((curmod, dsenv, env))::stack
in (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.push dsenv)
in (let env = (Microsoft_FStar_Tc_Env.push env msg)
in (go stack curmod dsenv env))))
end
| Code ((text, (ok, fail))) -> begin
(let mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.mark env)
in (dsenv, env))))
in (let reset_mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.reset_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.reset_mark env)
in (dsenv, env))))
in (let commit_mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.commit_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.commit_mark env)
in (dsenv, env))))
in (let fail = (fun curmod dsenv_mark env_mark -> (let _58_195 = ((Support.Prims.ignore) (Microsoft_FStar_Tc_Errors.report_all ()))
in (let _58_197 = (Support.ST.op_Colon_Equals Microsoft_FStar_Tc_Errors.num_errs 0)
in (let _58_199 = (Support.Microsoft.FStar.Util.fprint1 "%s\n" fail)
in (let _58_203 = (reset_mark dsenv_mark env_mark)
in (match (_58_203) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _58_206 = (mark dsenv env)
in (match (_58_206) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some ((curmod, dsenv, env)) -> begin
if ((! (Microsoft_FStar_Tc_Errors.num_errs)) = 0) then begin
(let _58_213 = (Support.Microsoft.FStar.Util.fprint1 "\n%s\n" ok)
in (let _58_217 = (commit_mark dsenv env)
in (match (_58_217) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _ -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env)))))))))

let batch_mode_tc = (fun filenames -> (let _58_224 = (tc_prims ())
in (match (_58_224) with
| (prims_mod, dsenv, env) -> begin
(let _58_239 = ((Support.List.fold_left (fun _58_228 f -> (match (_58_228) with
| (all_mods, dsenv, env) -> begin
(let _58_230 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let _58_235 = (tc_one_file dsenv env f)
in (match (_58_235) with
| (dsenv, env, ms) -> begin
((Support.List.append all_mods ms), dsenv, env)
end)))
end)) (prims_mod, dsenv, env)) filenames)
in (match (_58_239) with
| (all_mods, dsenv, env) -> begin
(let _58_240 = if ((! (Microsoft_FStar_Options.interactive)) && ((Microsoft_FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
end else begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end))
end)))

let finished_message = (fun fmods -> if (not ((! (Microsoft_FStar_Options.silent)))) then begin
(let msg = if (! (Microsoft_FStar_Options.verify)) then begin
"Verified"
end else begin
if (! (Microsoft_FStar_Options.pretype)) then begin
"Lax type-checked"
end else begin
"Parsed and desugared"
end
end
in (let _58_245 = ((Support.List.iter (fun m -> if (Microsoft_FStar_Options.should_verify m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str) then begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "%s module: %s\n" msg (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)))
end)) fmods)
in (Support.Microsoft.FStar.Util.print_string "All verification conditions discharged successfully\n")))
end)

let codegen = (fun fmods env -> if ((! (Microsoft_FStar_Options.codegen)) = Some ("OCaml")) then begin
(Support.Prims.try_with (fun _58_250 -> (match (_58_250) with
| () -> begin
(let mllib = (Microsoft_FStar_Backends_OCaml_ASTTrans.mlmod_of_fstars (Support.List.tail fmods))
in (let doc = (Microsoft_FStar_Backends_OCaml_Code.doc_of_mllib mllib)
in (Support.List.iter (fun _58_264 -> (match (_58_264) with
| (n, d) -> begin
(Support.Microsoft.FStar.Util.write_file (Microsoft_FStar_Options.prependOutputDir (Support.String.strcat n ".ml")) (FSharp_Format.pretty 120 d))
end)) doc)))
end)) (fun _58_249 -> (match (_58_249) with
| Microsoft_FStar_Backends_OCaml_ASTTrans.OCamlFailure ((rg, error)) -> begin
(let _58_256 = (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "OCaml Backend Error: %s %s\n" (Support.Microsoft.FStar.Range.string_of_range rg) (Microsoft_FStar_Backends_OCaml_ASTTrans.string_of_error error)))
in (exit (1)))
end)))
end else begin
if ((! (Microsoft_FStar_Options.codegen)) = Some ("OCaml-experimental")) then begin
(let tyDefns = (Microsoft_FStar_Backends_ML_Extraction.extractTypeDefns (Support.List.hd (Support.List.tl fmods)).Microsoft_FStar_Absyn_Syntax.declarations env)
in (let newDoc = (Microsoft_FStar_Backends_OCaml_Code.doc_of_sig tyDefns)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" (FSharp_Format.pretty 1 newDoc))))
end
end)

let go = (fun _58_267 -> (let _58_271 = (process_args ())
in (match (_58_271) with
| (res, filenames) -> begin
(match (res) with
| Support.Microsoft.FStar.Getopt.Help -> begin
(Microsoft_FStar_Options.display_usage (Microsoft_FStar_Options.specs ()))
end
| Support.Microsoft.FStar.Getopt.Die (msg) -> begin
(Support.Microsoft.FStar.Util.print_string msg)
end
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(let filenames = if ((! (Microsoft_FStar_Options.use_build_config)) || ((not ((! (Microsoft_FStar_Options.interactive)))) && ((Support.List.length filenames) = 1))) then begin
(match (filenames) with
| f::[] -> begin
(Microsoft_FStar_Parser_Driver.read_build_config f)
end
| _ -> begin
(let _58_280 = (Support.Microsoft.FStar.Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (exit (1)))
end)
end else begin
filenames
end
in (let _58_286 = (batch_mode_tc filenames)
in (match (_58_286) with
| (fmods, dsenv, env) -> begin
(let _58_287 = (report_errors None)
in if (! (Microsoft_FStar_Options.interactive)) then begin
(interactive_mode dsenv env)
end else begin
(let _58_289 = (codegen fmods env)
in (finished_message fmods))
end)
end)))
end)
end)))

let main = (fun _58_291 -> (match (_58_291) with
| () -> begin
(Support.Prims.try_with (fun _58_293 -> (match (_58_293) with
| () -> begin
(let _58_304 = (go ())
in (let _58_306 = (cleanup ())
in (exit (0))))
end)) (fun _58_292 -> (match (_58_292) with
| e -> begin
(let _58_296 = if (Microsoft_FStar_Absyn_Util.handleable e) then begin
(Microsoft_FStar_Absyn_Util.handle_err false () e)
end
in (let _58_298 = if (! (Microsoft_FStar_Options.trace_error)) then begin
(Support.Microsoft.FStar.Util.fprint2 "\nUnexpected error\n%s\n%s\n" (Support.Microsoft.FStar.Util.message_of_exn e) (Support.Microsoft.FStar.Util.trace_of_exn e))
end else begin
if (not ((Microsoft_FStar_Absyn_Util.handleable e))) then begin
(Support.Microsoft.FStar.Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Support.Microsoft.FStar.Util.message_of_exn e))
end
end
in (let _58_300 = (cleanup ())
in (exit (1)))))
end)))
end))




