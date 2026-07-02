#include <cmath>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

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
                      item->name, TypedefKindName(item->forward_type_kind)));
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

// Shared state for expanding the members of one enum typedef into backing
// variables and an ordered member list (§6.19 running-value semantics). Bundles
// the otherwise-many parameters the per-member helpers need.
struct EnumMemberBuilder {
  uint32_t width;
  Arena& arena;
  RtlirModule* mod;
  std::unordered_set<std::string_view>& enum_member_names;
  int64_t next_val = 0;
  std::vector<RtlirEnumMember> members = {};

  // Records one enum member (name + current value), reserving its name and
  // emitting a backing variable, then advances the running value.
  void EmitMember(std::string_view name) {
    enum_member_names.insert(name);
    members.push_back({name, next_val});
    RtlirVariable var;
    var.name = name;
    var.width = width;
    var.is_4state = false;
    // An enum element contributes its numeric value when read (§6.19.4); seed
    // the backing variable with that value rather than the default zero.
    auto* init = arena.Create<Expr>();
    init->kind = ExprKind::kIntegerLiteral;
    init->int_val = static_cast<uint64_t>(next_val);
    var.init_expr = init;
    mod->variables.push_back(var);
    ++next_val;
  }

  // Builds an arena-owned "<base><index>" name and emits it as a member.
  void EmitIndexedMember(std::string_view base, int64_t index) {
    auto s = std::format("{}{}", base, index);
    auto* p = arena.AllocString(s.c_str(), s.size());
    EmitMember(std::string_view{p, s.size()});
  }

  // Expands a `name[range_start:range_end]` member into one indexed member per
  // step from range_start toward range_end (inclusive).
  void EmitInclusiveRange(std::string_view name, int64_t n, int64_t m) {
    int step = (m >= n) ? 1 : -1;
    for (auto i = n;; i += step) {
      EmitIndexedMember(name, i);
      if (i == m) break;
    }
  }

  // Emits one declared enum member entry, expanding any `[range]` suffix.
  void EmitDeclaredMember(const EnumMember& member) {
    if (!member.range_start) {
      EmitMember(member.name);
      return;
    }
    auto n = ConstEvalInt(member.range_start).value_or(0);
    if (member.range_end) {
      EmitInclusiveRange(member.name, n,
                         ConstEvalInt(member.range_end).value_or(0));
    } else {
      for (int64_t i = 0; i < n; ++i) EmitIndexedMember(member.name, i);
    }
  }
};

// Expands the enum members of an enum typedef into backing variables and an
// ordered member list, reserving each member name. Mirrors the running-value
// semantics of §6.19 (explicit values, ranges, and implicit increments).
std::vector<RtlirEnumMember> BuildEnumMembers(
    ModuleItem* item, uint32_t width, Arena& arena, RtlirModule* mod,
    std::unordered_set<std::string_view>& enum_member_names) {
  EnumMemberBuilder builder{width, arena, mod, enum_member_names};
  for (const auto& member : item->typedef_type.enum_members) {
    if (member.value) {
      builder.next_val = ConstEvalInt(member.value).value_or(builder.next_val);
    }
    builder.EmitDeclaredMember(member);
  }
  return std::move(builder.members);
}

}  // namespace

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  if (HandleForwardTypedef(item, typedefs_, forward_typedef_kinds_, diag_)) {
    return;
  }
  auto it = forward_typedef_kinds_.find(item->name);
  if (it != forward_typedef_kinds_.end() &&
      it->second != item->typedef_type.kind) {
    diag_.Error(item->loc,
                std::format("typedef '{}' does not conform to its forward "
                            "declaration as {}",
                            item->name, TypedefKindName(it->second)));
  }
  typedefs_[item->name] = item->typedef_type;
  bool first_dim_assoc = IsAssocFirstDimTypedef(item, typedefs_, class_names_,
                                                assoc_typedef_names_);
  if (!item->unpacked_dims.empty() && !first_dim_assoc) {
    if (auto width = ComputeFixedUnpackedWidth(item, typedefs_)) {
      fixed_unpacked_typedef_widths_[item->name] = *width;
      td_array_dims_[item->name] = item->unpacked_dims;
    }
  }
  if (item->typedef_type.kind == DataTypeKind::kStruct ||
      item->typedef_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->typedef_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->typedef_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->typedef_type, item->loc,
                                         BuildParamScope(mod));
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  auto width = EvalTypeWidth(item->typedef_type, typedefs_);
  mod->enum_types[item->name] =
      BuildEnumMembers(item, width, arena_, mod, enum_member_names_);
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule*) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  if (!item->nettype_resolve_func.empty()) {
    nettype_resolve_funcs_[item->name] = item->nettype_resolve_func;
    nettype_canonical_[item->name] = item->name;
  } else if (item->typedef_type.kind == DataTypeKind::kNamed) {
    auto it = nettype_resolve_funcs_.find(item->typedef_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      nettype_resolve_funcs_[item->name] = it->second;
    }

    auto cit = nettype_canonical_.find(item->typedef_type.type_name);
    nettype_canonical_[item->name] = (cit != nettype_canonical_.end())
                                         ? cit->second
                                         : item->typedef_type.type_name;
  } else {
    nettype_canonical_[item->name] = item->name;
  }
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

// Emits enum-literal backing variables for every enum typedef in `pkg` that the
// importing module does not already define.
void EmitPackageEnumLiterals(const PackageDecl* pkg, RtlirModule* mod,
                             const ImportedEnumCtx& ctx) {
  for (auto* pi : pkg->items) {
    if (pi->kind != ModuleItemKind::kTypedef) continue;
    if (pi->typedef_type.kind != DataTypeKind::kEnum) continue;
    if (mod->enum_types.count(pi->name) != 0) continue;
    uint32_t width = EvalTypeWidth(pi->typedef_type, ctx.typedefs);
    mod->enum_types[pi->name] =
        BuildEnumMembers(pi, width, ctx.arena, mod, ctx.enum_member_names);
  }
}

}  // namespace

void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) continue;
    const PackageDecl* pkg =
        FindUnitPackage(ctx.unit, item->import_item.package_name);
    if (pkg) EmitPackageEnumLiterals(pkg, mod, ctx);
  }
}

}  // namespace delta
