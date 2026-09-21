#include <cmath>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Maps a typedef/forward kind to the noun used in conformance diagnostics.
std::string_view TypedefKindName(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kEnum:
      return "enum";
    case DataTypeKind::kStruct:
      return "struct";
    case DataTypeKind::kUnion:
      return "union";
    case DataTypeKind::kNamed:
      // §6.18: a forward class (or interface class) typedef records kNamed.
      return "class";
    default:
      return "type";
  }
}

// Handles a forward typedef declaration: optionally checks that a previously
// recorded definition conforms to the forward kind, records the forward kind,
// and reserves the name. Returns true if the item was a forward declaration
// (in which case the caller must stop processing).
//
// The name is reserved with try_emplace because §6.18 (printed page 118)
// admits a forward typedef before or after the final definition in the same
// scope, and a forward written after the definition must not put the
// placeholder over it. That keeps an entry of the same scope alone: a generate
// block's items are walked with the enclosing scope's table, and §27.5
// (printed 824) makes the block a scope of its own whose forward typedef
// stands over the enclosing scope's typedef of the name, so
// TakeEnclosingTypedefs in src/elaborator/elaborator_generate.cpp has taken
// the enclosing entry out before the walk reaches here. Until it did, a
// block's `typedef struct pair_t;` kept a module pair_t and the block's
// subroutine between the forward typedef and the definition resolved to it
// (found by a2d48456a's agent).
bool HandleForwardTypedef(
    ModuleItem* item, TypedefMap& typedefs,
    std::unordered_map<std::string_view, DataTypeKind>& forward_typedef_kinds,
    DiagEngine& diag) {
  if (item->typedef_type.kind != DataTypeKind::kImplicit) return false;
  if (item->forward_type_kind != DataTypeKind::kImplicit) {
    auto td_it = typedefs.find(item->name);
    if (td_it != typedefs.end() &&
        td_it->second.kind != DataTypeKind::kImplicit &&
        td_it->second.kind != item->forward_type_kind) {
      diag.Error(
          item->loc,
          std::format("forward typedef '{}' as {} does not conform "
                      "to its existing definition",
                      item->name, TypedefKindName(item->forward_type_kind)),
          Subclause("6.18"));
    }
    forward_typedef_kinds[item->name] = item->forward_type_kind;
  }
  typedefs.try_emplace(item->name, item->typedef_type);
  return true;
}

// §6.24.3: a typedef whose first unpacked dimension is an associative index.
// Detects the associative-index form and, if found, records the name so the
// bit-stream cast validator can reject it as a destination.
bool IsAssocFirstDimTypedef(
    ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names,
    std::unordered_set<std::string_view>& assoc_typedef_names) {
  if (item->unpacked_dims.empty() || !item->unpacked_dims[0] ||
      item->unpacked_dims[0]->kind != ExprKind::kIdentifier) {
    return false;
  }
  auto t = item->unpacked_dims[0]->text;
  bool is_assoc =
      (t == "string" || t == "int" || t == "integer" || t == "byte" ||
       t == "shortint" || t == "longint" || t == "*") ||
      (typedefs.count(t) > 0 || class_names.count(t) > 0);
  if (is_assoc) {
    assoc_typedef_names.insert(item->name);
  }
  return is_assoc;
}

// True when an identifier dimension names a dynamic/queue/associative form
// (so the enclosing typedef has no fixed bit width).
bool IsDynamicDimIdentifier(const Expr* dim) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  return t == "$" || t == "*" || t == "string" || t == "int" ||
         t == "integer" || t == "byte" || t == "shortint" || t == "longint";
}

// Computes the fixed element count contributed by a single unpacked dimension.
// Returns the count when the dimension is a fixed range or size, otherwise
// nullopt (dynamic, non-constant, or non-positive dimension).
std::optional<uint64_t> FixedDimCount(const Expr* dim) {
  if (!dim || IsDynamicDimIdentifier(dim)) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto lv = ConstEvalInt(dim->lhs);
    auto rv = ConstEvalInt(dim->rhs);
    if (!lv || !rv) return std::nullopt;
    int64_t span = std::abs(*lv - *rv) + 1;
    return static_cast<uint64_t>(span);
  }
  auto sv = ConstEvalInt(dim);
  if (!sv || *sv <= 0) return std::nullopt;
  return static_cast<uint64_t>(*sv);
}

// §6.24.3: when every unpacked dimension is a fixed integer size (no dynamic,
// queue, or associative dim), the typedef has a known total bit width.
// Returns the total width when fixed and representable, otherwise nullopt.
std::optional<uint32_t> ComputeFixedUnpackedWidth(ModuleItem* item,
                                                  const TypedefMap& typedefs) {
  uint32_t elem_width = EvalTypeWidth(item->typedef_type, typedefs);
  uint64_t total = elem_width;
  bool all_fixed = (elem_width > 0);
  for (auto* dim : item->unpacked_dims) {
    auto count = FixedDimCount(dim);
    if (!count) {
      all_fixed = false;
      break;
    }
    total *= *count;
  }
  if (all_fixed && total > 0 && total < uint64_t{1} << 32) {
    return static_cast<uint32_t>(total);
  }
  return std::nullopt;
}

// Where an enumeration's named constants are declared: the scope its member
// value expressions fold against, the arena its backing variables are allocated
// from, the module they are declared in, and the set that keeps one name from
// being declared twice. §6.19 makes the members constants of the enclosing
// scope rather than of the type, so all four describe that scope and travel
// together; the enumeration itself contributes only its members and its width.
struct EnumMemberDeclCtx {
  const ScopeMap& scope;
  Arena& arena;
  RtlirModule* mod;
  std::unordered_set<std::string_view>& enum_member_names;
  // §26.5: the names an explicit import of the scope has made locally visible,
  // which take precedence over the candidate a wildcard import supplies under
  // the same name (§26.3, printed page 810). A member so named keeps its place
  // in the type but declares no constant in this scope, so the bare name
  // reaches the explicitly imported literal. Null for the scope's own
  // enumeration, whose members are declared whatever the imports name.
  const std::unordered_set<std::string_view>* explicitly_imported = nullptr;
  // §6.19: the members are values of the enumeration's base type, `int` when
  // none is named, so each backing variable is signed when that type is
  // (IsSignedType of the enumeration); a read of a member under `%d` then
  // prints a negative value as such rather than as its bit pattern.
  bool is_signed = false;
};

// Declares an enumeration's named constants in a module: reserves each member
// name and emits a backing variable holding its value, since an enum element
// contributes its numeric value when read (§6.19.4). The values themselves --
// explicit values, ranges and implicit increments -- are folded by
// FoldEnumMembers in elaborator_enum_constants.cpp, which the package and
// compilation-unit scopes read as well. Takes the member list rather than the
// declaration holding it, because Syntax 6-5 makes the enum form a data_type:
// the same members can be written in a typedef or directly in a data
// declaration, and both declare the named constants.
std::vector<RtlirEnumMember> BuildEnumMembers(
    const std::vector<EnumMember>& decl_members, uint32_t width,
    const EnumMemberDeclCtx& ctx) {
  auto members = FoldEnumMembers(decl_members, ctx.scope, ctx.arena);
  for (const auto& member : members) {
    if (ctx.explicitly_imported != nullptr &&
        ctx.explicitly_imported->count(member.name) != 0)
      continue;
    ctx.enum_member_names.insert(member.name);
    RtlirVariable var;
    var.name = member.name;
    var.width = width;
    var.is_4state = false;
    var.is_signed = ctx.is_signed;
    auto* init = ctx.arena.Create<Expr>();
    init->kind = ExprKind::kIntegerLiteral;
    init->int_val = static_cast<uint64_t>(member.value);
    var.init_expr = init;
    ctx.mod->variables.push_back(var);
  }
  return members;
}

// The key mod->enum_types holds an enumeration under: the name of the typedef
// or variable declaring it, or, for an enumeration written as the type of a
// structure or union member of that declaration (ForEachEnumTypeIn's
// `member_path`), that name and the member's path joined with '.', which no
// typedef or variable is named. A variable's enum_type_name reaches the first
// form alone, so a variable of the structure's type is never taken for one of
// the member's enumeration.
std::string_view EnumTypeKey(std::string_view decl_name,
                             std::string_view member_path, Arena& arena) {
  if (member_path.empty()) return decl_name;
  auto* key = arena.Create<std::string>(std::string(decl_name) + "." +
                                        std::string(member_path));
  return *key;
}

// Declares the constants of the one enumeration `type` under `key`, and binds
// them in `scope` -- the map `ctx` folds against -- for an enumeration written
// after it in the same declaration, whose value §6.19 lets name an earlier
// enumeration's constant.
void DeclareEnumType(const DataType& type, std::string_view key, uint32_t width,
                     ScopeMap& scope, const EnumMemberDeclCtx& ctx) {
  auto members = BuildEnumMembers(type.enum_members, width, ctx);
  for (const auto& m : members) scope[m.name] = m.value;
  ctx.mod->enum_types[key] = std::move(members);
}

}  // namespace

// The shape rules a typedef's data type answers to wherever it is written: the
// packed-structure and union restrictions, and the rules on packed dimensions.
//
// `member_default_scope` is the parameter scope a struct member's default value
// is resolved against, or null when there is none to resolve against. Only a
// typedef inside a module has one, and the check is skipped without it rather
// than run against an empty scope, which would report every parameter
// reference as unresolvable.
void Elaborator::ValidateTypedefShape(const DataType& dtype, SourceLoc loc,
                                      const ScopeMap* member_default_scope) {
  if (dtype.kind == DataTypeKind::kStruct ||
      dtype.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(dtype, loc);
    ValidateUnpackedStructWithUnionDefaults(dtype, loc);
    if (member_default_scope != nullptr)
      ValidateStructMemberDefaultsConstant(dtype, loc, *member_default_scope);
    ValidateVoidMembers(dtype, loc);
    ValidateRandQualifiers(dtype, loc);
    ValidatePackedDimRequiresPackedKeyword(dtype, loc);
    ValidatePackedStructMemberTypes(dtype, loc);
    ValidateChandleInUnion(dtype, loc);
    ValidateVirtualInterfaceInUnion(dtype, loc);
    ValidatePackedUnion(dtype, loc);
  }
  ValidatePackedDimOnPredefinedType(dtype, loc);
  ValidatePackedDimOnDisallowedType(dtype, loc);
}

// §3.12: a typedef declared at compilation-unit scope is recorded in the type
// table when the compilation-unit scope is registered, and is never elaborated
// -- only a typedef reached through a module's item list runs ElaborateTypedef.
// Its shape is therefore never checked, and a declaration outside any module is
// accepted whatever it says. Driving the shape validations over those typedefs
// separately is what makes the rule apply wherever the typedef is written.
//
// The enum path of ElaborateTypedef has no counterpart here: it records the
// enumeration's members in a module, and a compilation-unit typedef has none.
void Elaborator::ValidateCuTypedefs() {
  for (auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    ValidateTypedefShape(item->typedef_type, item->loc,
                         /*member_default_scope=*/nullptr);
  }
}

// §6.18: "the type of the object is the type the name stands for", and §7.4.4
// keeps a typedef's unpacked dimensions in the type rather than in the
// declaration that uses the name -- `typedef bsix mem_type [0:3]` and
// `mem_type ba [0:7]` are the clause's own example of dimensions defined in
// stages. So `q_t qu;` declares a queue and `arr_t a;` four elements wherever
// either is written.
//
// AdoptTypedefArrayDims (elaborator_decls_var.cpp) gives those dimensions to a
// declaration written among a module's items. A declaration written inside a
// procedure is a Stmt and reached it nowhere, and the simulator's two
// procedural declaration paths read the statement's own dimensions and nothing
// else, so such a declaration was a plain variable of the element's type: a
// queue typedef declared a 32-bit vector and an unpacked-array typedef one
// element.
//
// The rewrite is the one the module-scope path makes -- the name's own type in
// place of the name, and the typedef's dimensions onto the declaration -- and
// it is made only where the declaration wrote no dimensions of its own, since
// §7.4.4's staging puts the declaration's own dimensions outside the typedef's
// and that is a shape this does not yet carry.
void Elaborator::AdoptTypedefDimsInStmt(Stmt* s) {
  if (s == nullptr) return;
  if ((s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) &&
      s->var_unpacked_dims.empty() &&
      s->var_decl_type.kind == DataTypeKind::kNamed) {
    auto dims = td_array_dims_.find(s->var_decl_type.type_name);
    auto base = typedefs_.find(s->var_decl_type.type_name);
    if (dims != td_array_dims_.end() && base != typedefs_.end()) {
      bool was_const = s->var_decl_type.is_const;
      s->var_decl_type = base->second;
      s->var_decl_type.is_const = was_const;
      s->var_unpacked_dims = dims->second;
    }
  }
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { AdoptTypedefDimsInStmt(sub); });
}

// Every procedure of a module, including the ones a generate construct holds:
// §27.6 makes a generate block's declarations declarations of the module, so a
// declaration written in one is written in the module's scope and stands under
// the same clause.
void Elaborator::AdoptProceduralTypedefDims(const ModuleDecl* decl) {
  std::function<void(ModuleItem*)> visit = [&](ModuleItem* item) {
    if (item == nullptr) return;
    AdoptTypedefDimsInStmt(item->body);
    for (auto* s : item->func_body_stmts) AdoptTypedefDimsInStmt(s);
    for (auto* child : item->gen_body) visit(child);
    visit(item->gen_else);
    for (auto& case_item : item->gen_case_items) {
      for (auto* child : case_item.body) visit(child);
    }
  };
  for (auto* item : decl->items) visit(item);
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  if (HandleForwardTypedef(item, typedefs_, forward_typedef_kinds_, diag_)) {
    return;
  }
  // §6.18 (printed page 118) ties the forward typedef's basic type to the
  // definition of the same scope, and §27.5 (printed 824) makes a generate
  // block a scope of its own, so the table holds the forward kinds of the
  // scope this definition stands in alone: TakeEnclosingTypedefs in
  // src/elaborator/elaborator_generate.cpp takes the enclosing scope's out
  // for a block's walk and erases the block's own after it. Until it did, a
  // block's forward kind stayed in the table and judged a sibling block's or
  // the enclosing block's definition of the name (found by b0ea40995's agent).
  auto it = forward_typedef_kinds_.find(item->name);
  if (it != forward_typedef_kinds_.end() &&
      it->second != item->typedef_type.kind) {
    diag_.Error(item->loc,
                std::format("typedef '{}' does not conform to its forward "
                            "declaration as {}",
                            item->name, TypedefKindName(it->second)),
                Subclause("6.18"));
  }
  typedefs_[item->name] = item->typedef_type;
  // §6.18: the dimensions belong to the type the name stands for, so a name
  // written with any of them stands for an aggregate rather than for one
  // element. Recording that is what lets the elaborated type-width table
  // decline to answer for it; the map below keeps only the dimensions of the
  // forms it was written for, and an associative typedef reaches neither.
  if (!item->unpacked_dims.empty()) {
    aggregate_typedef_names_.insert(item->name);
  }
  bool first_dim_assoc = IsAssocFirstDimTypedef(item, typedefs_, class_names_,
                                                assoc_typedef_names_);
  if (!item->unpacked_dims.empty() && !first_dim_assoc) {
    // §6.18: a typedef "gives a user-defined name to an existing data type",
    // and the clause has unpacked array types among those -- it notes that a
    // user-defined name is needed for a type parameter value "when unpacked
    // array types are used". So the dimensions belong to the type the name
    // stands for, and a variable declared with that name has them.
    //
    // Recording them is what carries them to such a variable. A queue or
    // dynamic dimension has no fixed width, so gating on one computing left
    // those two forms with nothing recorded and the dimension dropped
    // altogether: a variable declared through the typedef came out as the bare
    // element type rather than a queue or a dynamic array. The width is still
    // recorded only when it exists, since that is what it means.
    td_array_dims_[item->name] = item->unpacked_dims;
    if (auto width = ComputeFixedUnpackedWidth(item, typedefs_)) {
      fixed_unpacked_typedef_widths_[item->name] = *width;
    }
  }
  ScopeMap scope = BuildParamScope(mod);
  ValidateTypedefShape(item->typedef_type, item->loc, &scope);
  // §6.19 declares the constants in the scope holding the enumeration, whether
  // the typedef names the enumeration itself or a structure or union with an
  // enumeration written as a member's type (§7.2), which §23.9 makes no scope
  // of its own; ForEachEnumTypeIn reaches both. Each is checked as an
  // enumeration of the module and numbered on its own.
  ForEachEnumTypeIn(
      item->typedef_type, [&](std::string_view path, const DataType& type) {
        ValidateEnumDecl(type, item->loc, /*declares_its_constants=*/true);
        DeclareEnumType(type, EnumTypeKey(item->name, path, arena_),
                        EvalTypeWidth(type, typedefs_), scope,
                        {scope, arena_, mod, enum_member_names_, nullptr,
                         IsSignedType(type, typedefs_)});
      });
}

// §6.19: "An enumerated type declares a set of integral named constants", and
// Syntax 6-5 admits the enum form wherever a data_type may appear -- the
// clause's own example, `enum {red, yellow, green} light1, light2;`, declares
// red, yellow and green with no typedef in sight. Emit those constants for a
// data declaration written that way, so a later read of one finds its value.
//
// Several declarators may share one enumeration (light2 above repeats light1's
// members), and each arrives here as its own item carrying its own copy of the
// members. Emitting from the first declarator alone is what keeps one set of
// constants from being declared once per name in the list.
//
// A structure or union written as the declaration's type declares the
// constants of an enumeration written as a member's type the same way (§7.2,
// §23.9), `struct { enum {A, B} e; } s;` declaring A and B; ForEachEnumTypeIn
// reaches each. The enumeration written as the type itself is checked by
// ValidateVarDeclTypes ahead of this, so only a member's is checked here.
void Elaborator::EmitBareEnumMembers(const ModuleItem* item, RtlirModule* mod) {
  DataTypeKind kind = item->data_type.kind;
  if (kind != DataTypeKind::kEnum && kind != DataTypeKind::kStruct &&
      kind != DataTypeKind::kUnion)
    return;
  if (!item->first_in_decl_list) return;
  ScopeMap scope = BuildParamScope(mod);
  ForEachEnumTypeIn(
      item->data_type, [&](std::string_view path, const DataType& type) {
        if (type.enum_members.empty()) return;
        if (!path.empty())
          ValidateEnumDecl(type, item->loc, /*declares_its_constants=*/true);
        DeclareEnumType(type, EnumTypeKey(item->name, path, arena_),
                        EvalTypeWidth(type, typedefs_), scope,
                        {scope, arena_, mod, enum_member_names_, nullptr,
                         IsSignedType(type, typedefs_)});
      });
}

// §6.6.7: the data type of a user-defined nettype shall be a 4-state or 2-state
// integral type, a real or shortreal type, or a fixed-size unpacked aggregate
// of such types. The named-type forms (a typedef or an existing nettype named
// in the alias form) resolve to one of those and are accepted here; only the
// direct data types that can never be a legal nettype data type are rejected.
static bool IsIllegalNettypeDataTypeKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kChandle:
    case DataTypeKind::kEvent:
    case DataTypeKind::kVoid:
    case DataTypeKind::kVirtualInterface:
      return true;
    default:
      return false;
  }
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule*) {
  if (IsIllegalNettypeDataTypeKind(item->typedef_type.kind)) {
    diag_.Error(item->loc,
                std::format("data type of user-defined nettype '{}' is not a "
                            "legal nettype data type",
                            item->name),
                Subclause("6.6.7"));
  }
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  RegisterNettypeResolutionAndCanonical(item);

  // §6.6.7: a named resolution function shall return the nettype's data type
  // and take a single input argument that is a dynamic array (of that type).
  // Only a function resolvable in the current module scope is checked. The
  // structurally unambiguous facets -- exactly one argument, that argument not
  // being a fixed-size array, and a return type that does not name a different
  // type than the nettype -- are enforced through the shared signature
  // predicate. The lifetime and class-static facets are left unasserted here so
  // a conforming function is never rejected on a comparison this stage cannot
  // make precisely.
  if (!item->nettype_resolve_func.empty()) {
    CheckNettypeResolutionFunction(item);
  }
}

// §6.6.7: read the declared resolution function against the nettype it resolves
// and record which of the clause's requirements the signature meets.
//
// Two named types differing is a definite mismatch, and any other pairing --
// integral against real, or a named type against a matching builtin -- is left
// unasserted, because this stage cannot compare those precisely and a false
// rejection of a conforming function costs more than a missed report. Both the
// return type and the argument's element type are judged that way.
static NettypeResolutionSig BuildNettypeResolutionSig(const ModuleItem* item,
                                                      const ModuleItem* fn) {
  NettypeResolutionSig sig;
  const DataType& nettype_dt = item->typedef_type;
  const DataType& return_dt = fn->return_type;
  sig.return_type_matches_nettype = nettype_dt.kind != DataTypeKind::kNamed ||
                                    return_dt.kind != DataTypeKind::kNamed ||
                                    nettype_dt.type_name == return_dt.type_name;
  // §6.6.7's parenthetical "(or preserve no state information)" makes a
  // `static` lifetime alone no breach, so the lifetime keyword is not consulted
  // and this requirement is stated met.
  sig.is_automatic = true;
  sig.single_input_argument = fn->func_args.size() == 1;
  // The three argument requirements are stated met when there is no single
  // argument to judge, so the argument-count requirement is the one reported.
  sig.argument_is_input = true;
  sig.argument_is_dynamic_array = true;
  sig.argument_element_type_matches = true;
  if (!sig.single_input_argument) return sig;
  const FunctionArg& arg = fn->func_args[0];
  // §6.6.7 admits "a single input argument". Direction::kNone is the bare
  // `T driver[]` form, which §13.3 gives the default direction input.
  sig.argument_is_input =
      arg.direction == Direction::kInput || arg.direction == Direction::kNone;
  const bool kArgIsFixedArray =
      !arg.unpacked_dims.empty() && arg.unpacked_dims[0] != nullptr;
  sig.argument_is_dynamic_array = !kArgIsFixedArray;
  sig.argument_element_type_matches =
      nettype_dt.kind != DataTypeKind::kNamed ||
      arg.data_type.kind != DataTypeKind::kNamed ||
      nettype_dt.type_name == arg.data_type.type_name;
  return sig;
}

// §6.6.7: the sentence the report quotes, one per requirement the clause
// states. `func_name` names the resolution function, `nettype_name` the nettype
// it resolves and `data_type_name` the nettype's data type, which is the T the
// clause writes.
static std::string NettypeResolutionRuleMessage(
    NettypeResolutionRule rule, std::string_view func_name,
    std::string_view nettype_name, std::string_view data_type_name) {
  std::string prefix =
      std::format("resolution function '{}' of user-defined nettype '{}' ",
                  func_name, nettype_name);
  switch (rule) {
    case NettypeResolutionRule::kReturnType:
      return prefix +
             std::format("shall have a return type of '{}'", data_type_name);
    case NettypeResolutionRule::kArgumentCount:
      return prefix + "shall take a single input argument";
    case NettypeResolutionRule::kArgumentDirection:
      return prefix +
             "shall take a single input argument, and this one is not "
             "declared input";
    case NettypeResolutionRule::kArgumentIsDynamicArray:
      return prefix +
             "shall take an argument whose type is a dynamic array rather "
             "than a fixed-size array";
    case NettypeResolutionRule::kArgumentElementType:
      return prefix + std::format(
                          "shall take an argument that is a dynamic array of "
                          "elements of type '{}'",
                          data_type_name);
    case NettypeResolutionRule::kAutomaticLifetime:
      return prefix + "shall be automatic or preserve no state information";
    default:
      return prefix + "shall be a static class method";
  }
}

// §6.6.7's Syntax 6-1 writes the with clause as `with [ package_scope |
// class_scope ] tf_identifier`, so the search for a resolution function ends in
// one of three places, and which one it was is part of the answer: §6.6.7 rules
// that "while a class function method may be used for a resolution function,
// such functions shall be class static methods as the method call occurs in a
// context where no class object is involved in the call" (printed page 98 of
// IEEE 1800-2023), so whether the function is a class method decides
// which requirements it is held to.
//
// `scope_named_nothing` separates a qualifier that reaches neither a package
// nor a class from one that reaches a scope declaring no such function. They
// are different mistakes and get different reports.
struct NettypeResolutionTarget {
  const ModuleItem* fn = nullptr;
  bool is_class_method = false;
  bool is_static_method = false;
  bool scope_named_nothing = false;
};

// The function a class declares under `name`, whether or not it is static.
// §6.6.7 admits a non-static one as far as being found, and rejects it by the
// class-static rule rather than by not finding it, which is what lets the
// report say what is wrong with the source rather than that the name is
// missing.
static NettypeResolutionTarget ClassResolutionMethod(const ClassDecl* cls,
                                                     std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->method->name != name) continue;
    return {m->method, true, m->is_static, false};
  }
  return {nullptr, true, false, false};
}

// The function a package declares under `name`.
static const ModuleItem* PackageResolutionFunction(const PackageDecl* pkg,
                                                   std::string_view name) {
  for (const auto* pi : pkg->items) {
    if (pi->kind == ModuleItemKind::kFunctionDecl && pi->name == name)
      return pi;
  }
  return nullptr;
}

// The package `unit` declares under `name`, or null.
static const PackageDecl* FindNettypeScopePackage(const CompilationUnit* unit,
                                                  std::string_view name) {
  for (const auto* p : unit->packages) {
    if (p->name == name) return p;
  }
  return nullptr;
}

static NettypeResolutionTarget FindNettypeResolutionFunction(
    const ModuleItem* item, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  if (item->nettype_resolve_scope.empty()) {
    auto fit = func_decls.find(item->nettype_resolve_func);
    if (fit == func_decls.end()) return {};
    return {fit->second, false, false, false};
  }
  if (const ClassDecl* cls = FindClassDecl(item->nettype_resolve_scope, unit))
    return ClassResolutionMethod(cls, item->nettype_resolve_func);
  if (const PackageDecl* pkg =
          FindNettypeScopePackage(unit, item->nettype_resolve_scope))
    return {PackageResolutionFunction(pkg, item->nettype_resolve_func), false,
            false, false};
  return {nullptr, false, false, true};
}

void Elaborator::CheckNettypeResolutionFunction(const ModuleItem* item) {
  NettypeResolutionTarget target =
      FindNettypeResolutionFunction(item, unit_, func_decls_);
  // An unqualified name that is not found is left alone. func_decls_ holds the
  // functions of the design element being elaborated, so a name it does not
  // hold may still be declared somewhere this does not see; only a qualifier
  // says where the function was supposed to be, and so only a qualifier makes
  // its absence something this can report.
  if (!target.fn && item->nettype_resolve_scope.empty()) return;
  if (target.scope_named_nothing) {
    diag_.Error(item->loc,
                std::format("resolution function of user-defined nettype '{}' "
                            "names unknown package or class '{}'",
                            item->name, item->nettype_resolve_scope),
                Subclause("6.6.7"));
    return;
  }
  if (!target.fn) {
    diag_.Error(item->loc,
                std::format("resolution function '{}::{}' of user-defined "
                            "nettype '{}' does not exist",
                            item->nettype_resolve_scope,
                            item->nettype_resolve_func, item->name),
                Subclause("6.6.7"));
    return;
  }
  NettypeResolutionSig sig = BuildNettypeResolutionSig(item, target.fn);
  sig.is_class_method = target.is_class_method;
  sig.is_static_method = target.is_static_method;
  NettypeResolutionRule rule = ValidateNettypeResolutionFunction(sig);
  if (rule == NettypeResolutionRule::kConforming) return;
  diag_.Error(
      item->loc,
      NettypeResolutionRuleMessage(rule, item->nettype_resolve_func, item->name,
                                   item->typedef_type.type_name),
      Subclause("6.6.7"));
}

// §6.6.7: record the nettype's resolution function and its canonical (source)
// nettype. A nettype declared with `with f` resolves with f and is its own
// canonical source; a simple nettype that renames another inherits both that
// nettype's resolution function and its canonical name, so §6.22.6 matching
// reduces to comparing canonical names.
// §6.6.7: the resolution function's name as the with clause wrote it, qualifier
// included. The bare name alone cannot tell `with C::res` from `with res`, so a
// net of either nettype carried the same name into the simulator and two
// nettypes resolving through same-named functions in different scopes were
// indistinguishable there.
static std::string_view NettypeResolveFuncName(const ModuleItem* item,
                                               Arena& arena) {
  if (item->nettype_resolve_scope.empty()) return item->nettype_resolve_func;
  auto* qname =
      arena.Create<std::string>(std::string(item->nettype_resolve_scope) +
                                "::" + std::string(item->nettype_resolve_func));
  return *qname;
}

void Elaborator::RegisterNettypeResolutionAndCanonical(const ModuleItem* item) {
  if (!item->nettype_resolve_func.empty()) {
    nettype_resolve_funcs_[item->name] = NettypeResolveFuncName(item, arena_);
    nettype_canonical_[item->name] = item->name;
    return;
  }
  if (item->typedef_type.kind != DataTypeKind::kNamed) {
    nettype_canonical_[item->name] = item->name;
    return;
  }
  auto it = nettype_resolve_funcs_.find(item->typedef_type.type_name);
  if (it != nettype_resolve_funcs_.end()) {
    nettype_resolve_funcs_[item->name] = it->second;
  }
  auto cit = nettype_canonical_.find(item->typedef_type.type_name);
  nettype_canonical_[item->name] = (cit != nettype_canonical_.end())
                                       ? cit->second
                                       : item->typedef_type.type_name;
}

// §6.22.6 Matching nettypes: a nettype matches itself (and the nettype of nets
// declared using it), and a simple nettype that renames a user-defined nettype
// matches the nettype it renames. Both cases reduce to comparing the canonical
// (source) nettype each name resolves to: an alias shares its source's
// canonical name, so it matches; unrelated nettypes have distinct canonical
// names, so they do not.
bool NettypesMatch(std::string_view a, std::string_view b,
                   const std::unordered_map<std::string_view, std::string_view>&
                       nettype_canonical) {
  if (a == b) return true;
  auto ait = nettype_canonical.find(a);
  auto bit = nettype_canonical.find(b);
  std::string_view ca = (ait != nettype_canonical.end()) ? ait->second : a;
  std::string_view cb = (bit != nettype_canonical.end()) ? bit->second : b;
  return ca == cb;
}

namespace {

// Locates a package by name within the compilation unit, or nullptr.
const PackageDecl* FindUnitPackage(const CompilationUnit* unit,
                                   std::string_view name) {
  for (const auto* p : unit->packages) {
    if (p->name == name) return p;
  }
  return nullptr;
}

// Emits enum-literal backing variables for every enumeration an item among
// `items`, a package's or the compilation unit's, writes and the module does
// not already define, leaving out the members `explicitly_imported` names
// (§26.5). §6.19 (printed page 119) has an enumerated type declare its
// literals as constants of the scope holding it, and Syntax 6-5 makes the enum
// form a data_type, so a package's `enum {X, Y} v;` declares X and Y in the
// package as its `typedef enum {X, Y} t;` does, and §26.3 (printed 810) makes
// each a candidate the wildcard import brings in; ForEachEnumTypeOfItem reaches
// the type a typedef names and the type of a data declaration alike, and only
// the typedef's was walked before, so Y read through the import had no backing
// variable. A.2.1.3 gives one declaration several declarators, each its own
// item carrying the members again, and the first alone declares them.
void EmitEnumLiteralsOfItems(
    const std::vector<ModuleItem*>& items, RtlirModule* mod,
    const ImportedEnumCtx& ctx,
    const std::unordered_set<std::string_view>& explicitly_imported) {
  // A package's enum members fold against the package's own constants, which
  // this path does not carry; an empty scope keeps it to the literal values it
  // already resolved.
  ScopeMap no_scope;
  for (auto* pi : items) {
    if (!pi->first_in_decl_list) continue;
    // §6.19 with §7.2 and §23.9: an enumeration written as the type of a
    // member of a structure or union the item's type holds declares its
    // literals in the package as one written at the top does, and the
    // wildcard import brings each in; ForEachEnumTypeOfItem reaches both.
    ForEachEnumTypeOfItem(pi, [&](std::string_view path, const DataType& type) {
      std::string_view key = EnumTypeKey(pi->name, path, ctx.arena);
      if (mod->enum_types.count(key) != 0) return;
      uint32_t width = EvalTypeWidth(type, ctx.typedefs);
      mod->enum_types[key] = BuildEnumMembers(
          type.enum_members, width,
          {no_scope, ctx.arena, mod, ctx.enum_member_names,
           &explicitly_imported, IsSignedType(type, ctx.typedefs)});
    });
  }
}

// §26.3: the names the explicit imports among `items` make locally visible in
// the scope that wrote them, `import q::FALSE` naming FALSE.
std::unordered_set<std::string_view> ExplicitImportNames(
    const std::vector<ModuleItem*>& items) {
  std::unordered_set<std::string_view> names;
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard)
      names.insert(item->import_item.item_name);
  }
  return names;
}

}  // namespace

// The enumeration literals every wildcard import among `items` brings in, but
// for those `explicitly_imported` names.
static void EmitWildcardImportEnumLiterals(
    const std::vector<ModuleItem*>& items, RtlirModule* mod,
    const ImportedEnumCtx& ctx,
    const std::unordered_set<std::string_view>& explicitly_imported) {
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) continue;
    const PackageDecl* pkg =
        FindUnitPackage(ctx.unit, item->import_item.package_name);
    if (pkg) EmitEnumLiteralsOfItems(pkg->items, mod, ctx, explicitly_imported);
  }
}

// §26.3: a wildcard import brings a package's enumeration literals with it,
// whether the import stands in the module or, per §3.12.1, in the
// compilation-unit scope above it (Elaborator::ApplyCompilationUnitImports).
// §26.3 searches a scope's locally visible identifiers, an explicit import's
// among them, before the candidates its wildcard imports supply, and only then
// the outer scope (printed page 810), so an explicit import of the module
// shadows a wildcard's literal in the module and in the unit, and an explicit
// import of the unit shadows a wildcard's literal in the unit alone: the
// module's own wildcard candidate is found before the unit is searched.
void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx) {
  auto module_explicit = ExplicitImportNames(decl->items);
  auto unit_explicit = ExplicitImportNames(ctx.unit->cu_items);
  unit_explicit.insert(module_explicit.begin(), module_explicit.end());
  EmitWildcardImportEnumLiterals(ctx.unit->cu_items, mod, ctx, unit_explicit);
  EmitWildcardImportEnumLiterals(decl->items, mod, ctx, module_explicit);
}

// §23.9 finds a module's locally visible identifiers, an explicit import's
// among them, before the compilation-unit scope's declarations, so a literal
// of a unit-scope enumeration that the module's explicit import names is not
// declared in the module.
void RegisterCuEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                            const ImportedEnumCtx& ctx) {
  EmitEnumLiteralsOfItems(ctx.unit->cu_items, mod, ctx,
                          ExplicitImportNames(decl->items));
}

}  // namespace delta
