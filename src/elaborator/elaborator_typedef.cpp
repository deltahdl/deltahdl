#include <cmath>
#include <cstddef>
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
#include "elaborator/aggregate_shape.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/interface_port_typedef.h"
#include "elaborator/let_construct.h"
#include "elaborator/net_data_type.h"
#include "elaborator/nettype_registration.h"
#include "elaborator/nettype_resolution_lookup.h"
#include "elaborator/resolution_function_body.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
#include "lexer/token.h"
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
// compilation-unit scopes read as well. Takes the enumeration rather than the
// declaration holding it, because Syntax 6-5 makes the enum form a data_type:
// the same members can be written in a typedef or directly in a data
// declaration, and both declare the named constants. Each constant records
// the enumeration, which a type reference to it stands for (§6.23).
std::vector<RtlirEnumMember> BuildEnumMembers(const DataType& enumeration,
                                              uint32_t width,
                                              const EnumMemberDeclCtx& ctx) {
  auto members =
      FoldEnumMembers(enumeration.enum_members, ctx.scope, ctx.arena);
  for (auto& member : members) {
    member.enumeration = &enumeration;
    if (ctx.explicitly_imported != nullptr &&
        ctx.explicitly_imported->count(member.name) != 0)
      continue;
    ctx.enum_member_names.insert(member.name);
    RtlirVariable var;
    var.name = member.name;
    var.is_enum_constant = true;
    var.width = width;
    var.is_4state = false;
    var.is_signed = ctx.is_signed;
    if (member.xz_value != nullptr) {
      // §6.19: a member assigned x or z holds that value, which only a
      // 4-state constant can; the value is read as written, sized to the
      // enumeration as an assignment sizes it. Its integer fold read `'x` as
      // 0, and XX stood on IDLE's value.
      var.is_4state = true;
      var.init_expr = member.xz_value;
      ctx.mod->variables.push_back(var);
      continue;
    }
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
  auto members = BuildEnumMembers(type, width, ctx);
  for (const auto& m : members) scope[m.name] = m.value;
  ctx.mod->enum_types[key] = std::move(members);
}

}  // namespace

// The shape rules a typedef's data type answers to wherever it is written: the
// packed-structure and union restrictions, and the rules on packed dimensions.
//
// `member_default_scope` is the parameter scope a struct member's default value
// is resolved against, or null when there is none to resolve against: the
// module's parameters for a typedef inside a module, the compilation unit's for
// one written there. The check is skipped without one rather than run against
// an empty scope, which would report every parameter reference as
// unresolvable.
void Elaborator::ValidateTypedefShape(const DataType& dtype, SourceLoc loc,
                                      const ScopeMap* member_default_scope) {
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  CheckAggregateShape(dtype, loc, {kShapeTables, member_default_scope, diag_});
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
    // §7.2.2 holds a member default to a constant expression here as well,
    // which may name the compilation unit's own parameters (§11.2.1).
    ValidateTypedefShape(item->typedef_type, item->loc, &cu_param_scope_);
    CheckRealAssocIndexTypes(item->unpacked_dims, item->loc, typedefs_, diag_);
  }
}

// §6.18: an object declared with the name has the type the name stands for, and
// §7.4.4 keeps a typedef's unpacked dimensions in the type rather than in the
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
//
// A declaration that wrote dimensions of its own on such a name is marked
// instead (DataType::names_unpacked_array), so that the simulator takes an
// index past its element as the typedef's dimension rather than as a select
// within a packed element, as RtlirElementShape::type_is_unpacked_array tells
// it for the declaration among a module's items.
//
// §3.12.1 and §26.3: a name written behind a scope, `$unit::arr_t` or
// `p::arr_t`, is that scope's typedef whatever the module declares under the
// bare name, so it is looked up under the key the scope's typedef is recorded
// by (NamedTypeKey). Looked up by the bare name, it took the dimensions of the
// module's own arr_t.
void Elaborator::AdoptTypedefDimsInStmt(Stmt* s) {
  if (s == nullptr) return;
  if ((s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) &&
      s->var_decl_type.kind == DataTypeKind::kNamed) {
    const std::string kKey = NamedTypeKey(s->var_decl_type);
    auto dims = td_array_dims_.find(kKey);
    auto base = typedefs_.find(kKey);
    s->var_decl_type.names_unpacked_array =
        dims != td_array_dims_.end() && !s->var_unpacked_dims.empty();
    if (s->var_unpacked_dims.empty() && dims != td_array_dims_.end() &&
        base != typedefs_.end()) {
      bool was_const = s->var_decl_type.is_const;
      s->var_decl_type = base->second;
      s->var_decl_type.is_const = was_const;
      s->var_unpacked_dims = dims->second;
    }
  }
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { AdoptTypedefDimsInStmt(sub); });
}

// The key each of `item`'s formals takes its type by (NamedTypeKey), the name
// behind its scope where one is written, empty where it takes none by a name.
// A subroutine's formal takes its own; a let formal written with no type of
// its own takes the one written before it (§11.12 with §16.8), `b` of
// `let f(arr_t a, b)` arr_t, and so the dimensions with it.
static std::vector<std::string> FormalTypeKeys(const ModuleItem* item) {
  std::vector<const DataType*> types;
  if (item->kind == ModuleItemKind::kLetDecl) {
    types = LetFormalTypes(item->func_args);
  } else {
    for (const FunctionArg& arg : item->func_args)
      types.push_back(&arg.data_type);
  }
  std::vector<std::string> keys;
  keys.reserve(types.size());
  for (const DataType* type : types) {
    keys.push_back(type != nullptr && type->kind == DataTypeKind::kNamed
                       ? NamedTypeKey(*type)
                       : std::string{});
  }
  return keys;
}

// Every procedure of a module, including the ones a generate construct holds:
// §27.6 makes a generate block's declarations declarations of the module, so a
// declaration written in one is written in the module's scope and stands under
// the same clause.
//
// §13.4.1 and §13.5 with the same rule: a subroutine's formal declared by
// such a name, `arr_t a`, has the typedef's dimensions, as a declaration does,
// and a function whose return type is such a name records the dimensions and
// the element type beside the name (ModuleItem::return_array_dims), which
// keeps its width for the value the call yields. Left without them, a formal
// was one element to which an assignment pattern could not be distributed,
// and the implicit variable of the function one element wide, so `fn[1] = 8`
// and `return '{7, 8, 9}` handed the caller nothing.
//
// A let formal taking the type of the one before it, `b` of
// `let f(arr_t a, b)`, has the dimensions too, while only `a`'s type, the one
// written by the name, is rewritten to the element type, which `b` then reads
// through LetFormalTypes; the keys are read before any type is rewritten.
//
// A formal's or a return type's name written behind a scope, `$unit::arr_t`
// or `p::arr_t`, is looked up under that scope's key, as a procedural
// declaration's is (AdoptTypedefDimsInStmt).
static void AdoptSubroutineTypedefDims(
    ModuleItem* item,
    const std::unordered_map<std::string_view, std::vector<Expr*>>& td_dims,
    const TypedefMap& typedefs) {
  const std::vector<std::string> kKeys = FormalTypeKeys(item);
  for (size_t i = 0; i < kKeys.size(); ++i) {
    FunctionArg& arg = item->func_args[i];
    if (!arg.unpacked_dims.empty() || kKeys[i].empty()) continue;
    auto dims = td_dims.find(kKeys[i]);
    auto base = typedefs.find(kKeys[i]);
    if (dims == td_dims.end() || base == typedefs.end()) continue;
    if (arg.data_type.kind == DataTypeKind::kNamed)
      arg.data_type = base->second;
    arg.unpacked_dims = dims->second;
  }
  const DataType& ret = item->return_type;
  if (ret.kind != DataTypeKind::kNamed || !item->return_array_dims.empty())
    return;
  const std::string kReturnKey = NamedTypeKey(ret);
  auto dims = td_dims.find(kReturnKey);
  auto base = typedefs.find(kReturnKey);
  if (dims == td_dims.end() || base == typedefs.end()) return;
  item->return_array_dims = dims->second;
  item->return_array_elem_type = base->second;
}

void Elaborator::AdoptProceduralTypedefDims(const ModuleDecl* decl) {
  std::function<void(ModuleItem*)> visit = [&](ModuleItem* item) {
    if (item == nullptr) return;
    AdoptTypedefDimsInStmt(item->body);
    for (auto* s : item->func_body_stmts) AdoptTypedefDimsInStmt(s);
    AdoptSubroutineTypedefDims(item, td_array_dims_, typedefs_);
    for (auto* child : item->gen_body) visit(child);
    visit(item->gen_else);
    for (auto& case_item : item->gen_case_items) {
      for (auto* child : case_item.body) visit(child);
    }
  };
  for (auto* item : decl->items) visit(item);
}

// §7.2 with §7.4.4: a structure or union member declared with a typedef that
// carries unpacked dimensions, `a_t m1;` under `typedef bit a_t [3:0];`, has
// those dimensions, as the same member written out, `bit m1 [3:0]`, does. A
// member writing dimensions of its own keeps them. Left without them, the
// member was laid out and sized as one element.
static void AdoptMemberTypedefDims(
    DataType& type,
    const std::unordered_map<std::string_view, std::vector<Expr*>>& td_dims) {
  for (StructMember& m : type.struct_members) {
    if (m.type_kind != DataTypeKind::kNamed || !m.scope_name.empty() ||
        !m.unpacked_dims.empty())
      continue;
    auto dims = td_dims.find(m.type_name);
    if (dims != td_dims.end()) m.unpacked_dims = dims->second;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  // §6.23: `typedef type(x) t;` names the type x stands for, and everything
  // below judges and records that type. Unresolved, the type is implicit, the
  // mark of a forward typedef.
  ResolveTypeRef(item->typedef_type, item->loc, mod);
  // A.2.5 with §6.23: `typedef int t [type(k)];` is an associative array type
  // indexed by the type of k. The dimension is resolved here, ahead of the
  // record below that every variable `t x;` takes its dimensions from.
  ResolveTypeRefIndexDims(
      item->unpacked_dims,
      [&](DataType& type) { ResolveTypeRef(type, item->loc, mod); }, arena_);
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
  // §25.10: a type taken through an interface port stands for the
  // interface's own declaration of it, its enumeration members among it.
  if (!item->typedef_ifc_port.empty()) {
    const DataType* taken = InterfacePortTypedefType(
        item, module_decl_path_.back(),
        [this](std::string_view name) { return FindModuleInScope(name); });
    if (taken != nullptr) item->typedef_type = *taken;
  }
  AdoptMemberTypedefDims(item->typedef_type, td_array_dims_);
  SizeClassHandleMembers(item->typedef_type, typedefs_, class_names_);
  // §7.2 with §6.20: a member's dimensions may name the module's parameters,
  // which each instance binds to its own values, so the table this instance
  // reads the type through holds it with them folded; the declaration, which
  // every instance shares, keeps them as written.
  ScopeMap scope = BuildParamScope(mod);
  DataType recorded = item->typedef_type;
  FoldMemberDims(recorded, scope, arena_);
  RecordTypedef(typedefs_, item->name, recorded);
  // §6.18: the dimensions belong to the type the name stands for, so a name
  // written with any of them stands for an aggregate rather than for one
  // element. Recording that is what lets the elaborated type-width table
  // decline to answer for it.
  if (!item->unpacked_dims.empty()) {
    aggregate_typedef_names_.insert(item->name);
  }
  bool first_dim_assoc = IsAssocFirstDimTypedef(item, typedefs_, class_names_,
                                                assoc_typedef_names_);
  if (!item->unpacked_dims.empty()) {
    // §6.18: a typedef names an existing data type, and the clause has unpacked
    // array types among those -- it notes that a user-defined name is needed
    // for a type parameter value where unpacked array types are involved. So
    // the dimensions belong to the type the name stands for, and a variable
    // declared with that name has them.
    //
    // Recording them is what carries them to such a variable. A queue or
    // dynamic dimension has no fixed width, so gating on one computing left
    // those two forms with nothing recorded and the dimension dropped
    // altogether: a variable declared through the typedef came out as the bare
    // element type rather than a queue or a dynamic array. The width is still
    // recorded only when it exists, since that is what it means.
    //
    // §7.4.4 (printed page 155) and §7.8: an associative dimension is one of
    // them, so `ie_t x;` under `typedef bit ie_t[int];` is an associative
    // array indexed by int, as `bit x[int]` is. Left out of the record, it
    // declared a single bit, and `x[5] = 1` was reported as a bit-select of a
    // scalar.
    td_array_dims_[item->name] = item->unpacked_dims;
    if (!first_dim_assoc) {
      if (auto width = ComputeFixedUnpackedWidth(item, typedefs_)) {
        fixed_unpacked_typedef_widths_[item->name] = *width;
      }
    }
  }
  ValidateTypedefShape(item->typedef_type, item->loc, &scope);
  CheckRealAssocIndexTypes(item->unpacked_dims, item->loc, typedefs_, diag_);
  // §6.19 declares the constants in the scope holding the enumeration, whether
  // the typedef names the enumeration itself or a structure or union with an
  // enumeration written as a member's type (§7.2), which §23.9 makes no scope
  // of its own; ForEachEnumTypeIn reaches both. Each is checked as an
  // enumeration of the module and numbered on its own.
  ForEachEnumTypeIn(
      item->typedef_type, [&](std::string_view path, const DataType& type) {
        ValidateEnumDecl(type, item->loc, /*declares_its_constants=*/true);
        DeclareEnumType(type, EnumTypeKey(item->name, path, arena_),
                        EvalTypeWidth(EnumArrayElement(type), typedefs_), scope,
                        {scope, arena_, mod, enum_member_names_, nullptr,
                         IsSignedType(type, typedefs_)});
      });
}

// §6.19: an enumerated type declares a set of named integral constants, and
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
                        EvalTypeWidth(EnumArrayElement(type), typedefs_), scope,
                        {scope, arena_, mod, enum_member_names_, nullptr,
                         IsSignedType(type, typedefs_)});
      });
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod) {
  // §6.23: `nettype type(x) nt;` is a nettype of the type x stands for.
  ResolveTypeRef(item->typedef_type, item->loc, mod);
  // §6.6.7 judges the data type a nettype names, typedef names and all, and
  // IsLegalNettypeDataType in net_data_type.cpp says which those are.
  ReportIllegalNettypeDataType(*item, {typedefs_, td_array_dims_, class_names_},
                               diag_);
  // §6.6.7 with §8.25: a nettype's data type may be a structure a
  // parameterized class declares, named through a typedef of a
  // specialization, `MyBaseT::S`; the nettype is of that type as the
  // specialization binds it, as a variable declared with the name is.
  if (auto spec = SpecializeClassScopedType(
          item->typedef_type, unit_, BuildParamScope(mod), typedefs_, arena_))
    item->typedef_type = spec->type;
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
  // §6.6.7's parenthetical allowance for a function that keeps no state makes a
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
  // §6.6.7 admits exactly one input argument. Direction::kNone is the bare
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
                          "needs a dynamic array argument whose elements are "
                          "of type '{}'",
                          data_type_name);
    case NettypeResolutionRule::kAutomaticLifetime:
      return prefix +
             "has to be automatic, or else keep no state from one call to the "
             "next";
    default:
      return prefix + "shall be a static class method";
  }
}

void Elaborator::CheckNettypeResolutionFunction(const ModuleItem* item) {
  NettypeResolutionTarget target =
      FindNettypeResolutionFunction(item, unit_, func_decls_, typedefs_);
  // An unqualified name that is not found is left alone. func_decls_ holds the
  // functions of the design element being elaborated, so a name it does not
  // hold may still be declared somewhere this does not see; only a qualifier
  // says where the function was supposed to be, and so only a qualifier makes
  // its absence something this can report.
  if (!target.fn && item->nettype_resolve_scope == nullptr) return;
  if (target.scope_named_nothing) {
    diag_.Error(
        item->loc,
        std::format("resolution function of user-defined nettype '{}' "
                    "names unknown package or class '{}'",
                    item->name, NettypeScopeText(*item->nettype_resolve_scope)),
        Subclause("6.6.7"));
    return;
  }
  if (!target.fn) {
    diag_.Error(item->loc,
                std::format("resolution function '{}::{}' of user-defined "
                            "nettype '{}' does not exist",
                            NettypeScopeText(*item->nettype_resolve_scope),
                            item->nettype_resolve_func, item->name),
                Subclause("6.6.7"));
    return;
  }
  CheckResolutionFunctionBody(target.fn, diag_);
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

// §6.6.7 with §6.22.6: records the nettype's resolution function and the
// nettype it matches, under its own name, as RegisterNettype in
// nettype_registration.cpp records a module's, the compilation unit's and a
// package's nettypes alike.
void Elaborator::RegisterNettypeResolutionAndCanonical(const ModuleItem* item) {
  RegisterNettype(*item, item->name, {},
                  {nettype_names_, nettype_resolve_funcs_, nettype_canonical_},
                  arena_);
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
      uint32_t width = EvalTypeWidth(EnumArrayElement(type), ctx.typedefs);
      mod->enum_types[key] = BuildEnumMembers(
          type, width,
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
// module's own wildcard candidate is found before the unit is searched. The
// unit's imports written after the module are not in force in it (§3.12.1).
void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx) {
  const std::vector<ModuleItem*> kUnitBefore =
      UnitItemsBefore(ctx.unit, decl->range.start);
  auto module_explicit = ExplicitImportNames(decl->items);
  auto unit_explicit = ExplicitImportNames(kUnitBefore);
  unit_explicit.insert(module_explicit.begin(), module_explicit.end());
  EmitWildcardImportEnumLiterals(kUnitBefore, mod, ctx, unit_explicit);
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

void Elaborator::ReportUndeclaredTypeName(const ModuleItem* item) {
  if (!item->type_name_undeclared_at_parse) return;
  // One report per declaration rather than per declarator. A.2.1.3 gives
  // `data_declaration ::= [ const ] [ var ] [ lifetime ] data_type_or_implicit
  // list_of_variable_decl_assignments ;`, so `my_type a, b, c;` writes the
  // type_identifier once however many names follow it, and §6.18 is breached by
  // that one reference. Parser::ParseVarDeclList builds one ModuleItem per
  // declarator and marks each of them, so without this the source would be
  // reported as many times as it declares names.
  if (!item->first_in_decl_list) return;
  std::string_view name = item->data_type.type_name;
  // §23.3.2 gives module_instantiation its parenthesized list_of_port_
  // connections, so a name that does turn out to be a module was written as an
  // instantiation with that list left off.
  if (FindModuleInScope(name) != nullptr) {
    diag_.Error(
        item->loc,
        std::format("instantiation of module '{}' has no port connection list",
                    name),
        Subclause("23.3.2"));
    return;
  }
  // §6.18: a user-defined data type is declared before any reference to its
  // type_identifier. A type declared below this reference and a type declared
  // nowhere at all both breach it, and the sentence draws no distinction
  // between them: neither declaration precedes the reference.
  diag_.Error(item->loc,
              std::format("declaration of type '{}' does not precede this "
                          "reference to it",
                          name),
              Subclause("6.18"));
}

}  // namespace delta
