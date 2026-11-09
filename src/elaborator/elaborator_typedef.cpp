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
#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_variables.h"
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
#include "elaborator/procedural_typedef_shape.h"
#include "elaborator/resolution_function_body.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_scope_prefix.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/virtual_interface_target.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

std::string_view TypedefKindName(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kEnum:
      return "enum";
    case DataTypeKind::kStruct:
      return "struct";
    case DataTypeKind::kUnion:
      return "union";
    case DataTypeKind::kNamed:
      return "class";
    default:
      return "type";
  }
}

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

bool IsDynamicDimIdentifier(const Expr* dim) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  return t == "$" || t == "*" || t == "string" || t == "int" ||
         t == "integer" || t == "byte" || t == "shortint" || t == "longint";
}

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

struct EnumMemberDeclCtx {
  const ScopeMap& scope;
  Arena& arena;
  RtlirModule* mod;
  std::unordered_set<std::string_view>& enum_member_names;
  const std::unordered_set<std::string_view>* explicitly_imported = nullptr;
  bool is_signed = false;
  std::string_view gen_prefix = {};
};

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

std::string_view EnumTypeKey(std::string_view decl_name,
                             std::string_view member_path, Arena& arena) {
  if (member_path.empty()) return decl_name;
  auto* key = arena.Create<std::string>(std::string(decl_name) + "." +
                                        std::string(member_path));
  return *key;
}

void DeclareEnumType(const DataType& type, std::string_view key, uint32_t width,
                     ScopeMap& scope, const EnumMemberDeclCtx& ctx) {
  auto members = BuildEnumMembers(type, width, ctx);
  for (RtlirEnumMember m : members) {
    BindDeclaredConstant(scope, m.name, m.value);
    m.gen_block_prefix = ctx.gen_prefix;
    ctx.mod->enum_constants.push_back(m);
  }
  ctx.mod->enum_types[key] = std::move(members);
}

}  // namespace

void Elaborator::ValidateTypedefShape(const DataType& dtype, SourceLoc loc,
                                      const ScopeMap* member_default_scope) {
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  CheckAggregateShape(dtype, loc, {kShapeTables, member_default_scope, diag_});
  ValidatePackedDimOnPredefinedType(dtype, loc);
  ValidatePackedDimOnDisallowedType(dtype, loc);
  ValidateVirtualInterfaceType(
      dtype, loc,
      [this](std::string_view name) { return FindModuleInScope(name); }, diag_);
}

void Elaborator::ValidateCuTypedefs() {
  for (auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    ValidateTypedefShape(item->typedef_type, item->loc, &cu_param_scope_);
    CheckRealAssocIndexTypes(item->unpacked_dims, item->loc, typedefs_, diag_);
  }
}

void Elaborator::AdoptTypedefDimsInStmt(Stmt* s) {
  if (s == nullptr) return;
  if ((s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) &&
      s->var_decl_type.kind == DataTypeKind::kNamed) {
    auto shape = ArrayTypedefShape(
        s->var_decl_type,
        {typedefs_, td_array_dims_, unit_, procedural_typedef_scope_, arena_});
    s->var_decl_type.names_unpacked_array =
        shape.has_value() && !s->var_unpacked_dims.empty();
    if (s->var_unpacked_dims.empty() && shape.has_value()) {
      bool was_const = s->var_decl_type.is_const;
      s->var_decl_type = shape->type;
      s->var_decl_type.is_const = was_const;
      s->var_unpacked_dims = shape->unpacked_dims;
    }
  }
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { AdoptTypedefDimsInStmt(sub); });
}

static std::vector<std::optional<SpecializedClassType>> FormalTypeShapes(
    const ModuleItem* item, const ProceduralTypeScope& scope) {
  std::vector<const DataType*> types;
  if (item->kind == ModuleItemKind::kLetDecl) {
    types = LetFormalTypes(item->func_args);
  } else {
    for (const FunctionArg& arg : item->func_args)
      types.push_back(&arg.data_type);
  }
  std::vector<std::optional<SpecializedClassType>> shapes;
  shapes.reserve(types.size());
  for (const DataType* type : types) {
    shapes.push_back(type != nullptr && type->kind == DataTypeKind::kNamed
                         ? ArrayTypedefShape(*type, scope)
                         : std::nullopt);
  }
  return shapes;
}

static void AdoptSubroutineTypedefDims(ModuleItem* item,
                                       const ProceduralTypeScope& scope) {
  const std::vector<std::optional<SpecializedClassType>> kShapes =
      FormalTypeShapes(item, scope);
  for (size_t i = 0; i < kShapes.size(); ++i) {
    FunctionArg& arg = item->func_args[i];
    const std::optional<SpecializedClassType>& shape = kShapes[i];
    if (!arg.unpacked_dims.empty() || !shape.has_value()) continue;
    if (arg.data_type.kind == DataTypeKind::kNamed) arg.data_type = shape->type;
    arg.unpacked_dims = shape->unpacked_dims;
  }
  const DataType& ret = item->return_type;
  if (ret.kind != DataTypeKind::kNamed || !item->return_array_dims.empty())
    return;
  auto shape = ArrayTypedefShape(ret, scope);
  if (!shape.has_value()) return;
  item->return_array_dims = shape->unpacked_dims;
  item->return_array_elem_type = shape->type;
}

void Elaborator::AdoptProceduralTypedefDims(const ModuleDecl* decl) {
  const ProceduralTypeScope kScope{typedefs_, td_array_dims_, unit_,
                                   procedural_typedef_scope_, arena_};
  std::function<void(ModuleItem*)> visit = [&](ModuleItem* item) {
    if (item == nullptr) return;
    AdoptTypedefDimsInStmt(item->body);
    for (auto* s : item->func_body_stmts) AdoptTypedefDimsInStmt(s);
    AdoptSubroutineTypedefDims(item, kScope);
    for (auto* child : item->gen_body) visit(child);
    visit(item->gen_else);
    for (auto& case_item : item->gen_case_items) {
      for (auto* child : case_item.body) visit(child);
    }
  };
  for (auto* item : decl->items) visit(item);
}

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
  std::vector<Expr*> taken_dims =
      TypeRefUnpackedDims(item->typedef_type.type_ref_expr, mod);
  ResolveTypeRef(item->typedef_type, item->loc, mod);
  item->unpacked_dims.insert(item->unpacked_dims.end(), taken_dims.begin(),
                             taken_dims.end());
  ReportTypeParamPrefixNotAClass(item->typedef_type.scope_name, item->loc,
                                 {mod->params, typedefs_, class_names_, unit_},
                                 diag_);
  ReportSpecializationErrors(item->typedef_type, item->loc, mod);
  ResolveTypeRefIndexDims(
      item->unpacked_dims,
      [&](DataType& type) { ResolveTypeRef(type, item->loc, mod); }, arena_);
  if (HandleForwardTypedef(item, typedefs_, forward_typedef_kinds_, diag_)) {
    return;
  }
  auto it = forward_typedef_kinds_.find(item->name);
  if (it != forward_typedef_kinds_.end() &&
      it->second != item->typedef_type.kind) {
    diag_.Error(item->loc,
                std::format("typedef '{}' does not conform to its forward "
                            "declaration as {}",
                            item->name, TypedefKindName(it->second)),
                Subclause("6.18"));
  }
  if (!item->typedef_ifc_port.empty()) {
    const ModuleItem* taken = InterfacePortTypedef(
        item, module_decl_path_.back(),
        [this](std::string_view name) { return FindModuleInScope(name); });
    if (taken != nullptr) {
      item->typedef_type = taken->typedef_type;
      item->unpacked_dims.insert(item->unpacked_dims.end(),
                                 taken->unpacked_dims.begin(),
                                 taken->unpacked_dims.end());
    }
  }
  AdoptMemberTypedefDims(item->typedef_type, td_array_dims_);
  SizeClassHandleMembers(item->typedef_type, typedefs_, class_names_);
  ScopeMap scope = BuildParamScope(mod);
  DataType recorded = item->typedef_type;
  FoldMemberDims(recorded, scope, arena_);
  RecordTypedef(typedefs_, item->name, recorded);
  if (!item->unpacked_dims.empty()) {
    aggregate_typedef_names_.insert(item->name);
  }
  bool first_dim_assoc = IsAssocFirstDimTypedef(item, typedefs_, class_names_,
                                                assoc_typedef_names_);
  if (!item->unpacked_dims.empty()) {
    td_array_dims_[item->name] = item->unpacked_dims;
    if (!first_dim_assoc) {
      if (auto width = ComputeFixedUnpackedWidth(item, typedefs_)) {
        fixed_unpacked_typedef_widths_[item->name] = *width;
      }
    }
  } else {
    td_array_dims_.erase(item->name);
  }
  ValidateTypedefShape(item->typedef_type, item->loc, &scope);
  CheckRealAssocIndexTypes(item->unpacked_dims, item->loc, typedefs_, diag_);
  ForEachEnumTypeIn(
      item->typedef_type, [&](std::string_view path, const DataType& type) {
        ValidateEnumDecl(type, item->loc, true);
        DeclareEnumType(type, EnumTypeKey(item->name, path, arena_),
                        EvalTypeWidth(EnumArrayElement(type), typedefs_), scope,
                        {scope, arena_, mod, enum_member_names_, nullptr,
                         IsSignedType(type, typedefs_), InternedGenPrefix()});
      });
}

void Elaborator::EmitBareEnumMembers(const ModuleItem* item, RtlirModule* mod) {
  if (!item->first_in_decl_list) return;
  EmitInPlaceEnumMembers(item->data_type, item->name, item->loc, mod);
}

void Elaborator::EmitInPlaceEnumMembers(const DataType& type,
                                        std::string_view key, SourceLoc loc,
                                        RtlirModule* mod) {
  if (type.kind != DataTypeKind::kEnum && type.kind != DataTypeKind::kStruct &&
      type.kind != DataTypeKind::kUnion)
    return;
  ScopeMap scope = BuildParamScope(mod);
  ForEachEnumTypeIn(type, [&](std::string_view path, const DataType& found) {
    if (found.enum_members.empty()) return;
    if (!path.empty()) ValidateEnumDecl(found, loc, true);
    DeclareEnumType(found, EnumTypeKey(key, path, arena_),
                    EvalTypeWidth(EnumArrayElement(found), typedefs_), scope,
                    {scope, arena_, mod, enum_member_names_, nullptr,
                     IsSignedType(found, typedefs_), InternedGenPrefix()});
  });
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item->typedef_type, item->loc, mod);
  ReportIllegalNettypeDataType(*item, {typedefs_, td_array_dims_, class_names_},
                               diag_, [&](std::string_view name) {
                                 return VisibleCovergroup(name, mod, unit_) !=
                                        nullptr;
                               });
  if (auto spec = SpecializeClassScopedType(
          item->typedef_type, unit_, BuildParamScope(mod), typedefs_, arena_))
    item->typedef_type = spec->type;
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  RegisterNettypeResolutionAndCanonical(item);

  if (!item->nettype_resolve_func.empty()) {
    CheckNettypeResolutionFunction(item);
  }
}

static NettypeResolutionSig BuildNettypeResolutionSig(const ModuleItem* item,
                                                      const ModuleItem* fn) {
  NettypeResolutionSig sig;
  const DataType& nettype_dt = item->typedef_type;
  const DataType& return_dt = fn->return_type;
  sig.return_type_matches_nettype = nettype_dt.kind != DataTypeKind::kNamed ||
                                    return_dt.kind != DataTypeKind::kNamed ||
                                    nettype_dt.type_name == return_dt.type_name;
  sig.is_automatic = true;
  sig.single_input_argument = fn->func_args.size() == 1;
  sig.argument_is_input = true;
  sig.argument_is_dynamic_array = true;
  sig.argument_element_type_matches = true;
  if (!sig.single_input_argument) return sig;
  const FunctionArg& arg = fn->func_args[0];
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

void Elaborator::RegisterNettypeResolutionAndCanonical(const ModuleItem* item) {
  RegisterNettype(*item, item->name, {},
                  {nettype_names_, nettype_resolve_funcs_, nettype_canonical_},
                  arena_);
}

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

const PackageDecl* FindUnitPackage(const CompilationUnit* unit,
                                   std::string_view name) {
  for (const auto* p : unit->packages) {
    if (p->name == name) return p;
  }
  return nullptr;
}

void EmitEnumLiteralsOfItems(
    const std::vector<ModuleItem*>& items, RtlirModule* mod,
    const ImportedEnumCtx& ctx,
    const std::unordered_set<std::string_view>& explicitly_imported) {
  ScopeMap no_scope;
  for (auto* pi : items) {
    if (!pi->first_in_decl_list) continue;
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

std::unordered_set<std::string_view> ShadowingNames(const ModuleDecl* decl) {
  auto names = ExplicitImportNames(decl->items);
  for (const ModuleItem* item : decl->items) {
    ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
      for (const EnumMember& member : type.enum_members)
        names.insert(member.name);
    });
  }
  return names;
}

}  // namespace

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

void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx) {
  const std::vector<ModuleItem*> kUnitBefore =
      UnitItemsBefore(ctx.unit, decl->range.start);
  auto module_explicit = ShadowingNames(decl);
  auto unit_explicit = ExplicitImportNames(kUnitBefore);
  unit_explicit.insert(module_explicit.begin(), module_explicit.end());
  EmitWildcardImportEnumLiterals(kUnitBefore, mod, ctx, unit_explicit);
  EmitWildcardImportEnumLiterals(decl->items, mod, ctx, module_explicit);
}

void RegisterCuEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                            const ImportedEnumCtx& ctx) {
  EmitEnumLiteralsOfItems(UnitItemsBefore(ctx.unit, decl->range.start), mod,
                          ctx, ShadowingNames(decl));
}

void Elaborator::ReportUndeclaredTypeName(const ModuleItem* item) {
  if (!item->type_name_undeclared_at_parse) return;
  if (!item->first_in_decl_list) return;
  std::string_view name = item->data_type.type_name;
  if (FindModuleInScope(name) != nullptr) {
    diag_.Error(
        item->loc,
        std::format("instantiation of module '{}' has no port connection list",
                    name),
        Subclause("23.3.2"));
    return;
  }
  diag_.Error(item->loc,
              std::format("declaration of type '{}' does not precede this "
                          "reference to it",
                          name),
              Subclause("6.18"));
}

}  // namespace delta
