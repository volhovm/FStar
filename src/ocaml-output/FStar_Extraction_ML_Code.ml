
open Prims
# 32 "FStar.Extraction.ML.Code.fst"
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 35 "FStar.Extraction.ML.Code.fst"
let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
type fixity =
| Prefix
| Postfix
| Infix of assoc

# 36 "FStar.Extraction.ML.Code.fst"
let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_73_3) -> begin
_73_3
end))

# 36 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 37 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 38 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 40 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 42 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 44 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 54 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 55 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 56 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 57 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 59 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 60 "FStar.Extraction.ML.Code.fst"
let rec in_ns = (fun x -> (match (x) with
| ([], _73_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_73_18, _73_20) -> begin
false
end))

# 69 "FStar.Extraction.ML.Code.fst"
let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (
# 73 "FStar.Extraction.ML.Code.fst"
let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(
# 76 "FStar.Extraction.ML.Code.fst"
let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (
# 77 "FStar.Extraction.ML.Code.fst"
let ns_len = (FStar_List.length ns)
in (
# 78 "FStar.Extraction.ML.Code.fst"
let found = (FStar_Util.find_map cg_libs (fun cg_path -> (
# 79 "FStar.Extraction.ML.Code.fst"
let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(
# 81 "FStar.Extraction.ML.Code.fst"
let _73_31 = (FStar_Util.first_N cg_len ns)
in (match (_73_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _162_31 = (let _162_30 = (let _162_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_162_29)::[])
in (FStar_List.append pfx _162_30))
in Some (_162_31))
end else begin
None
end
end))
end else begin
None
end)))
in (match (found) with
| None -> begin
(ns')::[]
end
| Some (x) -> begin
x
end))))
end))

# 88 "FStar.Extraction.ML.Code.fst"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _73_41 -> begin
(
# 95 "FStar.Extraction.ML.Code.fst"
let _73_44 = x
in (match (_73_44) with
| (ns, x) -> begin
(let _162_36 = (path_of_ns currentModule ns)
in (_162_36, x))
end))
end))

# 96 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _162_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _162_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 101 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 107 "FStar.Extraction.ML.Code.fst"
let _73_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_50) with
| (p, s) -> begin
(let _162_46 = (let _162_45 = (let _162_44 = (ptsym_of_symbol s)
in (_162_44)::[])
in (FStar_List.append p _162_45))
in (FStar_String.concat "." _162_46))
end))
end)

# 108 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 112 "FStar.Extraction.ML.Code.fst"
let _73_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_55) with
| (p, s) -> begin
(
# 113 "FStar.Extraction.ML.Code.fst"
let s = if ((let _162_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _162_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 114 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 132 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 139 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 142 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 150 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 154 "FStar.Extraction.ML.Code.fst"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _73_60 -> (match (_73_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_66 -> (match (_73_66) with
| (y, _73_63, _73_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 161 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 165 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_70 -> (match (_73_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_74 -> (match (_73_74) with
| (y, _73_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 172 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 176 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _73_78 -> (match (_73_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_82 -> (match (_73_82) with
| (y, _73_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 183 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 187 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_86 -> (match (_73_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_90 -> (match (_73_90) with
| (y, _73_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 194 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 198 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _73_94 inner doc -> (match (_73_94) with
| (outer, side) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 203 "FStar.Extraction.ML.Code.fst"
let _73_103 = _inner
in (match (_73_103) with
| (pi, fi) -> begin
(
# 204 "FStar.Extraction.ML.Code.fst"
let _73_106 = _outer
in (match (_73_106) with
| (po, fo) -> begin
((pi > po) || (match ((fi, side)) with
| (Postfix, Left) -> begin
true
end
| (Prefix, Right) -> begin
true
end
| (Infix (Left), Left) -> begin
((pi = po) && (fo = Infix (Left)))
end
| (Infix (Right), Right) -> begin
((pi = po) && (fo = Infix (Right)))
end
| (Infix (Left), ILeft) -> begin
((pi = po) && (fo = Infix (Left)))
end
| (Infix (Right), IRight) -> begin
((pi = po) && (fo = Infix (Right)))
end
| (_73_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_73_134, _73_136) -> begin
false
end))
end))
end)))
in if (noparens inner outer side) then begin
doc
end else begin
(FStar_Format.parens doc)
end)
end))

# 217 "FStar.Extraction.ML.Code.fst"
let ocaml_u8_codepoint : FStar_BaseTypes.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 221 "FStar.Extraction.ML.Code.fst"
let encode_char : FStar_BaseTypes.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(
# 226 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.string_of_char c)
in (
# 227 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.unicode_of_string bytes)
in (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
end else begin
(match (c) with
| c when (c = '\\') -> begin
"\\\\"
end
| c when (c = ' ') -> begin
" "
end
| c when (c = '\b') -> begin
"\\b"
end
| c when (c = '\t') -> begin
"\\t"
end
| c when (c = '\r') -> begin
"\\r"
end
| c when (c = '\n') -> begin
"\\n"
end
| c when (c = '\'') -> begin
"\\\'"
end
| c when (c = '\"') -> begin
"\\\""
end
| c when (FStar_Util.is_letter_or_digit c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_punctuation c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_symbol c) -> begin
(FStar_Util.string_of_char c)
end
| _73_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 242 "FStar.Extraction.ML.Code.fst"
let string_of_mlconstant : FStar_Extraction_ML_Syntax.mlconstant  ->  Prims.string = (fun sctt -> (match (sctt) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"()"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (true) -> begin
"true"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (false) -> begin
"false"
end
| FStar_Extraction_ML_Syntax.MLC_Char (c) -> begin
(let _162_92 = (let _162_91 = (encode_char c)
in (Prims.strcat "\'" _162_91))
in (Prims.strcat _162_92 "\'"))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int8))) | (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int16))) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
if (FStar_ST.read FStar_Options.use_native_int) then begin
s
end else begin
(Prims.strcat (Prims.strcat "(Prims.parse_int \"" s) "\")")
end
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(
# 261 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(
# 265 "FStar.Extraction.ML.Code.fst"
let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end
| _73_205 -> begin
(FStar_All.failwith "TODO: extract integer constants properly into OCaml")
end))

# 268 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 275 "FStar.Extraction.ML.Code.fst"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _162_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _162_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 282 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 283 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_107 = (let _162_106 = (let _162_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_105 doc))
in (FStar_Format.hbox _162_106))
in (FStar_Format.parens _162_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 287 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _73_225 -> begin
(
# 292 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _162_110 = (let _162_109 = (let _162_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_108 args))
in (FStar_Format.hbox _162_109))
in (FStar_Format.parens _162_110)))
end)
in (
# 297 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _162_112 = (let _162_111 = (as_standard_type name)
in (FStar_Option.get _162_111))
in (Prims.snd _162_112))
end else begin
(ptsym currentModule name)
end
in (let _162_116 = (let _162_115 = (let _162_114 = (let _162_113 = (FStar_Format.text name)
in (_162_113)::[])
in (args)::_162_114)
in (FStar_Format.reduce1 _162_115))
in (FStar_Format.hbox _162_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_231, t2) -> begin
(
# 307 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 308 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _162_121 = (let _162_120 = (let _162_119 = (let _162_118 = (let _162_117 = (FStar_Format.text " -> ")
in (_162_117)::(d2)::[])
in (d1)::_162_118)
in (FStar_Format.reduce1 _162_119))
in (FStar_Format.hbox _162_120))
in (maybe_paren outer t_prio_fun _162_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _162_125 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _162_125)))

# 317 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 323 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_148 = (let _162_147 = (let _162_146 = (FStar_Format.text "Prims.checked_cast")
in (_162_146)::(doc)::[])
in (FStar_Format.reduce _162_147))
in (FStar_Format.parens _162_148))
end else begin
(let _162_153 = (let _162_152 = (let _162_151 = (FStar_Format.text "Obj.magic ")
in (let _162_150 = (let _162_149 = (FStar_Format.parens doc)
in (_162_149)::[])
in (_162_151)::_162_150))
in (FStar_Format.reduce _162_152))
in (FStar_Format.parens _162_153))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 329 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 330 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _162_157 = (let _162_156 = (let _162_155 = (FStar_Format.text ";")
in (_162_155)::(FStar_Format.hardline)::[])
in (d)::_162_156)
in (FStar_Format.reduce _162_157))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _162_158 = (string_of_mlconstant c)
in (FStar_Format.text _162_158))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_259) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _162_159 = (ptsym currentModule path)
in (FStar_Format.text _162_159))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 343 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_271 -> (match (_73_271) with
| (name, e) -> begin
(
# 344 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_166 = (let _162_165 = (let _162_162 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_162))
in (let _162_164 = (let _162_163 = (FStar_Format.text "=")
in (_162_163)::(doc)::[])
in (_162_165)::_162_164))
in (FStar_Format.reduce1 _162_166)))
end))
in (let _162_169 = (let _162_168 = (FStar_Format.text "; ")
in (let _162_167 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_168 _162_167)))
in (FStar_Format.cbrackets _162_169)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 350 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_171 = (let _162_170 = (as_standard_constructor ctor)
in (FStar_Option.get _162_170))
in (Prims.snd _162_171))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 358 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_173 = (let _162_172 = (as_standard_constructor ctor)
in (FStar_Option.get _162_172))
in (Prims.snd _162_173))
end else begin
(ptctor currentModule ctor)
end
in (
# 363 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 364 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _162_177 = (let _162_176 = (FStar_Format.parens x)
in (let _162_175 = (let _162_174 = (FStar_Format.text "::")
in (_162_174)::(xs)::[])
in (_162_176)::_162_175))
in (FStar_Format.reduce _162_177))
end
| (_73_290, _73_292) -> begin
(let _162_183 = (let _162_182 = (FStar_Format.text name)
in (let _162_181 = (let _162_180 = (let _162_179 = (let _162_178 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_178 args))
in (FStar_Format.parens _162_179))
in (_162_180)::[])
in (_162_182)::_162_181))
in (FStar_Format.reduce1 _162_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 372 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 373 "FStar.Extraction.ML.Code.fst"
let docs = (let _162_185 = (let _162_184 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_184 docs))
in (FStar_Format.parens _162_185))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 377 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _162_188 = (let _162_187 = (let _162_186 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_162_186)::[])
in (FStar_Format.hardline)::_162_187)
in (FStar_Format.reduce _162_188))
end else begin
FStar_Format.empty
end
in (
# 382 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 383 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _162_195 = (let _162_194 = (let _162_193 = (let _162_192 = (let _162_191 = (let _162_190 = (let _162_189 = (FStar_Format.text "in")
in (_162_189)::(body)::[])
in (FStar_Format.reduce1 _162_190))
in (_162_191)::[])
in (doc)::_162_192)
in (pre)::_162_193)
in (FStar_Format.combine FStar_Format.hardline _162_194))
in (FStar_Format.parens _162_195)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (_73_332::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _73_330; FStar_Extraction_ML_Syntax.loc = _73_328}::{FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((arg, _73_320)::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _73_317; FStar_Extraction_ML_Syntax.loc = _73_315}::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(
# 392 "FStar.Extraction.ML.Code.fst"
let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _73_347; FStar_Extraction_ML_Syntax.loc = _73_345}, branches); FStar_Extraction_ML_Syntax.mlty = _73_343; FStar_Extraction_ML_Syntax.loc = _73_341} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
branches
end
| e -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild, None, e))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try ((scrutinee, branches)); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_366; FStar_Extraction_ML_Syntax.loc = _73_364}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_386; FStar_Extraction_ML_Syntax.loc = _73_384}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _73_398 -> begin
(
# 415 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 416 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _162_196 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _162_196))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 421 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 422 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_201 = (let _162_200 = (let _162_199 = (FStar_Format.text ".")
in (let _162_198 = (let _162_197 = (FStar_Format.text (Prims.snd f))
in (_162_197)::[])
in (_162_199)::_162_198))
in (e)::_162_200)
in (FStar_Format.reduce _162_201))
end else begin
(let _162_207 = (let _162_206 = (let _162_205 = (FStar_Format.text ".")
in (let _162_204 = (let _162_203 = (let _162_202 = (ptsym currentModule f)
in (FStar_Format.text _162_202))
in (_162_203)::[])
in (_162_205)::_162_204))
in (e)::_162_206)
in (FStar_Format.reduce _162_207))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 429 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_223 = (let _162_222 = (FStar_Format.text "(")
in (let _162_221 = (let _162_220 = (FStar_Format.text x)
in (let _162_219 = (let _162_218 = (match (xt) with
| Some (xxt) -> begin
(let _162_215 = (let _162_214 = (FStar_Format.text " : ")
in (let _162_213 = (let _162_212 = (doc_of_mltype currentModule outer xxt)
in (_162_212)::[])
in (_162_214)::_162_213))
in (FStar_Format.reduce1 _162_215))
end
| _73_417 -> begin
(FStar_Format.text "")
end)
in (let _162_217 = (let _162_216 = (FStar_Format.text ")")
in (_162_216)::[])
in (_162_218)::_162_217))
in (_162_220)::_162_219))
in (_162_222)::_162_221))
in (FStar_Format.reduce1 _162_223))
end else begin
(FStar_Format.text x)
end)
in (
# 435 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _73_423 -> (match (_73_423) with
| ((x, _73_420), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 436 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 437 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_230 = (let _162_229 = (FStar_Format.text "fun")
in (let _162_228 = (let _162_227 = (FStar_Format.reduce1 ids)
in (let _162_226 = (let _162_225 = (FStar_Format.text "->")
in (_162_225)::(body)::[])
in (_162_227)::_162_226))
in (_162_229)::_162_228))
in (FStar_Format.reduce1 _162_230))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 441 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 442 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_243 = (let _162_242 = (let _162_237 = (let _162_236 = (FStar_Format.text "if")
in (let _162_235 = (let _162_234 = (let _162_233 = (FStar_Format.text "then")
in (let _162_232 = (let _162_231 = (FStar_Format.text "begin")
in (_162_231)::[])
in (_162_233)::_162_232))
in (cond)::_162_234)
in (_162_236)::_162_235))
in (FStar_Format.reduce1 _162_237))
in (let _162_241 = (let _162_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_239 = (let _162_238 = (FStar_Format.text "end")
in (_162_238)::[])
in (_162_240)::_162_239))
in (_162_242)::_162_241))
in (FStar_Format.combine FStar_Format.hardline _162_243))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 452 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 453 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_266 = (let _162_265 = (let _162_250 = (let _162_249 = (FStar_Format.text "if")
in (let _162_248 = (let _162_247 = (let _162_246 = (FStar_Format.text "then")
in (let _162_245 = (let _162_244 = (FStar_Format.text "begin")
in (_162_244)::[])
in (_162_246)::_162_245))
in (cond)::_162_247)
in (_162_249)::_162_248))
in (FStar_Format.reduce1 _162_250))
in (let _162_264 = (let _162_263 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_262 = (let _162_261 = (let _162_256 = (let _162_255 = (FStar_Format.text "end")
in (let _162_254 = (let _162_253 = (FStar_Format.text "else")
in (let _162_252 = (let _162_251 = (FStar_Format.text "begin")
in (_162_251)::[])
in (_162_253)::_162_252))
in (_162_255)::_162_254))
in (FStar_Format.reduce1 _162_256))
in (let _162_260 = (let _162_259 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _162_258 = (let _162_257 = (FStar_Format.text "end")
in (_162_257)::[])
in (_162_259)::_162_258))
in (_162_261)::_162_260))
in (_162_263)::_162_262))
in (_162_265)::_162_264))
in (FStar_Format.combine FStar_Format.hardline _162_266))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 465 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 466 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 467 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_273 = (let _162_272 = (let _162_271 = (FStar_Format.text "match")
in (let _162_270 = (let _162_269 = (FStar_Format.parens cond)
in (let _162_268 = (let _162_267 = (FStar_Format.text "with")
in (_162_267)::[])
in (_162_269)::_162_268))
in (_162_271)::_162_270))
in (FStar_Format.reduce1 _162_272))
in (_162_273)::pats)
in (
# 468 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _162_278 = (let _162_277 = (FStar_Format.text "raise")
in (let _162_276 = (let _162_275 = (let _162_274 = (ptctor currentModule exn)
in (FStar_Format.text _162_274))
in (_162_275)::[])
in (_162_277)::_162_276))
in (FStar_Format.reduce1 _162_278))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 476 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _162_287 = (let _162_286 = (FStar_Format.text "raise")
in (let _162_285 = (let _162_284 = (let _162_279 = (ptctor currentModule exn)
in (FStar_Format.text _162_279))
in (let _162_283 = (let _162_282 = (let _162_281 = (let _162_280 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_280 args))
in (FStar_Format.parens _162_281))
in (_162_282)::[])
in (_162_284)::_162_283))
in (_162_286)::_162_285))
in (FStar_Format.reduce1 _162_287)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _162_296 = (let _162_295 = (FStar_Format.text "try")
in (let _162_294 = (let _162_293 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_292 = (let _162_291 = (FStar_Format.text "with")
in (let _162_290 = (let _162_289 = (let _162_288 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _162_288))
in (_162_289)::[])
in (_162_291)::_162_290))
in (_162_293)::_162_292))
in (_162_295)::_162_294))
in (FStar_Format.combine FStar_Format.hardline _162_296))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 487 "FStar.Extraction.ML.Code.fst"
let _73_471 = (let _162_301 = (as_bin_op p)
in (FStar_Option.get _162_301))
in (match (_73_471) with
| (_73_468, prio, txt) -> begin
(
# 488 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 489 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 490 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_304 = (let _162_303 = (let _162_302 = (FStar_Format.text txt)
in (_162_302)::(e2)::[])
in (e1)::_162_303)
in (FStar_Format.reduce1 _162_304))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 494 "FStar.Extraction.ML.Code.fst"
let _73_481 = (let _162_308 = (as_uni_op p)
in (FStar_Option.get _162_308))
in (match (_73_481) with
| (_73_479, txt) -> begin
(
# 495 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 496 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_312 = (let _162_311 = (FStar_Format.text txt)
in (let _162_310 = (let _162_309 = (FStar_Format.parens e1)
in (_162_309)::[])
in (_162_311)::_162_310))
in (FStar_Format.reduce1 _162_312))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _162_315 = (string_of_mlconstant c)
in (FStar_Format.text _162_315))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 506 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_498 -> (match (_73_498) with
| (name, p) -> begin
(let _162_324 = (let _162_323 = (let _162_318 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_318))
in (let _162_322 = (let _162_321 = (FStar_Format.text "=")
in (let _162_320 = (let _162_319 = (doc_of_pattern currentModule p)
in (_162_319)::[])
in (_162_321)::_162_320))
in (_162_323)::_162_322))
in (FStar_Format.reduce1 _162_324))
end))
in (let _162_327 = (let _162_326 = (FStar_Format.text "; ")
in (let _162_325 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_326 _162_325)))
in (FStar_Format.cbrackets _162_327)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 510 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_329 = (let _162_328 = (as_standard_constructor ctor)
in (FStar_Option.get _162_328))
in (Prims.snd _162_329))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 518 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_331 = (let _162_330 = (as_standard_constructor ctor)
in (FStar_Option.get _162_330))
in (Prims.snd _162_331))
end else begin
(ptctor currentModule ctor)
end
in (
# 523 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _162_337 = (let _162_336 = (doc_of_pattern currentModule x)
in (let _162_335 = (let _162_334 = (FStar_Format.text "::")
in (let _162_333 = (let _162_332 = (doc_of_pattern currentModule xs)
in (_162_332)::[])
in (_162_334)::_162_333))
in (_162_336)::_162_335))
in (FStar_Format.reduce _162_337))
end
| (_73_515, FStar_Extraction_ML_Syntax.MLP_Tuple (_73_517)::[]) -> begin
(let _162_342 = (let _162_341 = (FStar_Format.text name)
in (let _162_340 = (let _162_339 = (let _162_338 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _162_338))
in (_162_339)::[])
in (_162_341)::_162_340))
in (FStar_Format.reduce1 _162_342))
end
| _73_522 -> begin
(let _162_349 = (let _162_348 = (FStar_Format.text name)
in (let _162_347 = (let _162_346 = (let _162_345 = (let _162_344 = (FStar_Format.text ", ")
in (let _162_343 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _162_344 _162_343)))
in (FStar_Format.parens _162_345))
in (_162_346)::[])
in (_162_348)::_162_347))
in (FStar_Format.reduce1 _162_349))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 532 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _162_351 = (let _162_350 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_350 ps))
in (FStar_Format.parens _162_351)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 536 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 537 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _162_352 = (FStar_Format.text " | ")
in (FStar_Format.combine _162_352 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _73_535 -> (match (_73_535) with
| (p, cond, e) -> begin
(
# 542 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _162_358 = (let _162_357 = (FStar_Format.text "|")
in (let _162_356 = (let _162_355 = (doc_of_pattern currentModule p)
in (_162_355)::[])
in (_162_357)::_162_356))
in (FStar_Format.reduce1 _162_358))
end
| Some (c) -> begin
(
# 546 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _162_364 = (let _162_363 = (FStar_Format.text "|")
in (let _162_362 = (let _162_361 = (doc_of_pattern currentModule p)
in (let _162_360 = (let _162_359 = (FStar_Format.text "when")
in (_162_359)::(c)::[])
in (_162_361)::_162_360))
in (_162_363)::_162_362))
in (FStar_Format.reduce1 _162_364)))
end)
in (let _162_375 = (let _162_374 = (let _162_369 = (let _162_368 = (let _162_367 = (FStar_Format.text "->")
in (let _162_366 = (let _162_365 = (FStar_Format.text "begin")
in (_162_365)::[])
in (_162_367)::_162_366))
in (case)::_162_368)
in (FStar_Format.reduce1 _162_369))
in (let _162_373 = (let _162_372 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_371 = (let _162_370 = (FStar_Format.text "end")
in (_162_370)::[])
in (_162_372)::_162_371))
in (_162_374)::_162_373))
in (FStar_Format.combine FStar_Format.hardline _162_375)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _73_545 -> (match (_73_545) with
| (rec_, top_level, lets) -> begin
(
# 557 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_553 -> (match (_73_553) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_550; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 558 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 559 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 563 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _73_559 -> (match (_73_559) with
| (x, _73_558) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 564 "FStar.Extraction.ML.Code.fst"
let ty_annot = if (not (pt)) then begin
(FStar_Format.text "")
end else begin
if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (Some (_::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 572 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_382 = (let _162_381 = (FStar_Format.text ":")
in (_162_381)::(ty)::[])
in (FStar_Format.reduce1 _162_382)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 583 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_384 = (let _162_383 = (FStar_Format.text ":")
in (_162_383)::(ty)::[])
in (FStar_Format.reduce1 _162_384)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _162_391 = (let _162_390 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _162_389 = (let _162_388 = (FStar_Format.reduce1 ids)
in (let _162_387 = (let _162_386 = (let _162_385 = (FStar_Format.text "=")
in (_162_385)::(e)::[])
in (ty_annot)::_162_386)
in (_162_388)::_162_387))
in (_162_390)::_162_389))
in (FStar_Format.reduce1 _162_391))))))
end))
in (
# 589 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _162_395 = (let _162_394 = (FStar_Format.text "let")
in (let _162_393 = (let _162_392 = (FStar_Format.text "rec")
in (_162_392)::[])
in (_162_394)::_162_393))
in (FStar_Format.reduce1 _162_395))
end else begin
(FStar_Format.text "let")
end
in (
# 591 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 592 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _162_399 = (let _162_398 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_162_398)::(doc)::[])
in (FStar_Format.reduce1 _162_399))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _73_599 -> (match (_73_599) with
| (lineno, file) -> begin
if ((FStar_ST.read FStar_Options.no_location_info) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 603 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _162_406 = (let _162_405 = (FStar_Format.text "#")
in (let _162_404 = (let _162_403 = (FStar_Format.num lineno)
in (let _162_402 = (let _162_401 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_162_401)::[])
in (_162_403)::_162_402))
in (_162_405)::_162_404))
in (FStar_Format.reduce1 _162_406)))
end
end))

# 604 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 608 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_607 -> (match (_73_607) with
| (x, tparams, body) -> begin
(
# 609 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _73_612 -> begin
(
# 614 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _162_415 = (let _162_414 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_414 doc))
in (FStar_Format.parens _162_415)))
end)
in (
# 617 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 623 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _73_625 -> (match (_73_625) with
| (name, ty) -> begin
(
# 624 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 625 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_422 = (let _162_421 = (let _162_420 = (FStar_Format.text ":")
in (_162_420)::(ty)::[])
in (name)::_162_421)
in (FStar_Format.reduce1 _162_422))))
end))
in (let _162_425 = (let _162_424 = (FStar_Format.text "; ")
in (let _162_423 = (FStar_List.map forfield fields)
in (FStar_Format.combine _162_424 _162_423)))
in (FStar_Format.cbrackets _162_425)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 632 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _73_633 -> (match (_73_633) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _73_636 -> begin
(
# 636 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 637 "FStar.Extraction.ML.Code.fst"
let tys = (let _162_428 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_428 tys))
in (let _162_432 = (let _162_431 = (FStar_Format.text name)
in (let _162_430 = (let _162_429 = (FStar_Format.text "of")
in (_162_429)::(tys)::[])
in (_162_431)::_162_430))
in (FStar_Format.reduce1 _162_432))))
end)
end))
in (
# 641 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 642 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _162_435 = (let _162_434 = (FStar_Format.text "|")
in (_162_434)::(d)::[])
in (FStar_Format.reduce1 _162_435))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 647 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_439 = (let _162_438 = (let _162_437 = (let _162_436 = (ptsym currentModule ([], x))
in (FStar_Format.text _162_436))
in (_162_437)::[])
in (tparams)::_162_438)
in (FStar_Format.reduce1 _162_439))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 652 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _162_444 = (let _162_443 = (let _162_442 = (let _162_441 = (let _162_440 = (FStar_Format.text "=")
in (_162_440)::[])
in (doc)::_162_441)
in (FStar_Format.reduce1 _162_442))
in (_162_443)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _162_444)))
end))))
end))
in (
# 657 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 658 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _162_449 = (let _162_448 = (FStar_Format.text "type")
in (let _162_447 = (let _162_446 = (let _162_445 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _162_445 doc))
in (_162_446)::[])
in (_162_448)::_162_447))
in (FStar_Format.reduce1 _162_449))
end else begin
(FStar_Format.text "")
end
in doc))))

# 659 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _162_469 = (let _162_468 = (let _162_461 = (let _162_460 = (FStar_Format.text "module")
in (let _162_459 = (let _162_458 = (FStar_Format.text x)
in (let _162_457 = (let _162_456 = (FStar_Format.text "=")
in (_162_456)::[])
in (_162_458)::_162_457))
in (_162_460)::_162_459))
in (FStar_Format.reduce1 _162_461))
in (let _162_467 = (let _162_466 = (doc_of_sig currentModule subsig)
in (let _162_465 = (let _162_464 = (let _162_463 = (let _162_462 = (FStar_Format.text "end")
in (_162_462)::[])
in (FStar_Format.reduce1 _162_463))
in (_162_464)::[])
in (_162_466)::_162_465))
in (_162_468)::_162_467))
in (FStar_Format.combine FStar_Format.hardline _162_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _162_473 = (let _162_472 = (FStar_Format.text "exception")
in (let _162_471 = (let _162_470 = (FStar_Format.text x)
in (_162_470)::[])
in (_162_472)::_162_471))
in (FStar_Format.reduce1 _162_473))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 674 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 675 "FStar.Extraction.ML.Code.fst"
let args = (let _162_475 = (let _162_474 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_474 args))
in (FStar_Format.parens _162_475))
in (let _162_481 = (let _162_480 = (FStar_Format.text "exception")
in (let _162_479 = (let _162_478 = (FStar_Format.text x)
in (let _162_477 = (let _162_476 = (FStar_Format.text "of")
in (_162_476)::(args)::[])
in (_162_478)::_162_477))
in (_162_480)::_162_479))
in (FStar_Format.reduce1 _162_481))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_667, ty)) -> begin
(
# 679 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_487 = (let _162_486 = (FStar_Format.text "val")
in (let _162_485 = (let _162_484 = (FStar_Format.text x)
in (let _162_483 = (let _162_482 = (FStar_Format.text ": ")
in (_162_482)::(ty)::[])
in (_162_484)::_162_483))
in (_162_486)::_162_485))
in (FStar_Format.reduce1 _162_487)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 687 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 688 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 689 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _162_498 = (let _162_497 = (FStar_Format.text "exception")
in (let _162_496 = (let _162_495 = (FStar_Format.text x)
in (_162_495)::[])
in (_162_497)::_162_496))
in (FStar_Format.reduce1 _162_498))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 699 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 700 "FStar.Extraction.ML.Code.fst"
let args = (let _162_500 = (let _162_499 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_499 args))
in (FStar_Format.parens _162_500))
in (let _162_506 = (let _162_505 = (FStar_Format.text "exception")
in (let _162_504 = (let _162_503 = (FStar_Format.text x)
in (let _162_502 = (let _162_501 = (FStar_Format.text "of")
in (_162_501)::(args)::[])
in (_162_503)::_162_502))
in (_162_505)::_162_504))
in (FStar_Format.reduce1 _162_506))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _162_514 = (let _162_513 = (FStar_Format.text "let")
in (let _162_512 = (let _162_511 = (FStar_Format.text "_")
in (let _162_510 = (let _162_509 = (FStar_Format.text "=")
in (let _162_508 = (let _162_507 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_162_507)::[])
in (_162_509)::_162_508))
in (_162_511)::_162_510))
in (_162_513)::_162_512))
in (FStar_Format.reduce1 _162_514))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 716 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 720 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 721 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_73_707) -> begin
FStar_Format.empty
end
| _73_710 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 723 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _73_713 -> (match (_73_713) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 727 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _73_720 -> (match (_73_720) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 728 "FStar.Extraction.ML.Code.fst"
let head = (let _162_533 = (let _162_532 = (FStar_Format.text "module")
in (let _162_531 = (let _162_530 = (FStar_Format.text x)
in (let _162_529 = (let _162_528 = (FStar_Format.text ":")
in (let _162_527 = (let _162_526 = (FStar_Format.text "sig")
in (_162_526)::[])
in (_162_528)::_162_527))
in (_162_530)::_162_529))
in (_162_532)::_162_531))
in (FStar_Format.reduce1 _162_533))
in (
# 729 "FStar.Extraction.ML.Code.fst"
let tail = (let _162_535 = (let _162_534 = (FStar_Format.text "end")
in (_162_534)::[])
in (FStar_Format.reduce1 _162_535))
in (
# 730 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _73_726 -> (match (_73_726) with
| (s, _73_725) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 731 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 732 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _162_545 = (let _162_544 = (FStar_Format.cat head FStar_Format.hardline)
in (let _162_543 = (let _162_542 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_541 = (let _162_540 = (FStar_Format.reduce sub)
in (let _162_539 = (let _162_538 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_538)::[])
in (_162_540)::_162_539))
in (_162_542)::_162_541))
in (_162_544)::_162_543))
in (FStar_Format.reduce _162_545)))))))
end))
and for1_mod = (fun istop _73_739 -> (match (_73_739) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 743 "FStar.Extraction.ML.Code.fst"
let head = (let _162_558 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_550 = (FStar_Format.text "module")
in (let _162_549 = (let _162_548 = (FStar_Format.text x)
in (_162_548)::[])
in (_162_550)::_162_549))
end else begin
if (not (istop)) then begin
(let _162_557 = (FStar_Format.text "module")
in (let _162_556 = (let _162_555 = (FStar_Format.text x)
in (let _162_554 = (let _162_553 = (FStar_Format.text "=")
in (let _162_552 = (let _162_551 = (FStar_Format.text "struct")
in (_162_551)::[])
in (_162_553)::_162_552))
in (_162_555)::_162_554))
in (_162_557)::_162_556))
end else begin
[]
end
end
in (FStar_Format.reduce1 _162_558))
in (
# 748 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _162_560 = (let _162_559 = (FStar_Format.text "end")
in (_162_559)::[])
in (FStar_Format.reduce1 _162_560))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 751 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _73_745 -> (match (_73_745) with
| (_73_743, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 752 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 753 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 754 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_564 = (let _162_563 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _162_563 FStar_Format.hardline))
in (_162_564)::[])
end else begin
[]
end
in (let _162_576 = (let _162_575 = (let _162_574 = (let _162_573 = (let _162_572 = (FStar_Format.text "open Prims")
in (let _162_571 = (let _162_570 = (let _162_569 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_568 = (let _162_567 = (FStar_Format.reduce sub)
in (let _162_566 = (let _162_565 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_565)::[])
in (_162_567)::_162_566))
in (_162_569)::_162_568))
in (FStar_Format.hardline)::_162_570)
in (_162_572)::_162_571))
in (FStar_Format.hardline)::_162_573)
in (head)::_162_574)
in (FStar_List.append prefix _162_575))
in (FStar_All.pipe_left FStar_Format.reduce _162_576))))))))
end))
in (
# 770 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _73_757 -> (match (_73_757) with
| (x, s, m) -> begin
(let _162_578 = (for1_mod true (x, s, m))
in (x, _162_578))
end)) mllib)
in docs))
end))

# 771 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 775 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 778 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_585 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _162_585 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 779 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 782 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_590 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _162_590 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))




