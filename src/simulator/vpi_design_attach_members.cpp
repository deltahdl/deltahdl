#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_packed_arrays.h"
#include "simulator/vpi_design_attach_vars.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_named_type_kinds.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

int VpiDataTypeVariableKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
      return vpiByteVar;
    case DataTypeKind::kShortint:
      return vpiShortIntVar;
    case DataTypeKind::kInt:
      return vpiIntVar;
    case DataTypeKind::kLongint:
      return vpiLongIntVar;
    case DataTypeKind::kInteger:
      return vpiIntegerVar;
    case DataTypeKind::kTime:
      return vpiTimeVar;
    case DataTypeKind::kBit:
      return vpiBitVar;
    case DataTypeKind::kStruct:
      return vpiStructVar;
    case DataTypeKind::kUnion:
      return vpiUnionVar;
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return vpiRealVar;
    case DataTypeKind::kShortreal:
      return vpiShortRealVar;
    case DataTypeKind::kString:
      return vpiStringVar;
    case DataTypeKind::kChandle:
      return vpiChandleVar;
    case DataTypeKind::kEnum:
      return vpiEnumVar;
    case DataTypeKind::kEvent:
      return vpiNamedEvent;
    case DataTypeKind::kVirtualInterface:
      return vpiVirtualInterfaceVar;
    default:
      return kVpiReg;
  }
}

namespace {

bool NamesClass(const RtlirDesign& design,
                const std::vector<ClassDecl*>& classes, std::string_view name) {
  static constexpr std::string_view kBuiltIn[] = {"process", "semaphore",
                                                  "mailbox"};
  const auto kIsNamed = [name](std::string_view cls) { return cls == name; };
  const auto kDeclares = [&](const std::vector<ClassDecl*>& decls) {
    return std::ranges::any_of(decls, [&](const ClassDecl* decl) {
      return decl != nullptr && kIsNamed(decl->name);
    });
  };
  return kDeclares(classes) || kDeclares(design.cu_class_decls) ||
         std::ranges::any_of(kBuiltIn, kIsNamed);
}

int NamedTypeKind(const RtlirDesign& design, bool names_class,
                  std::string_view key) {
  if (names_class || design.type_targets.contains(key)) return vpiClassVar;
  const auto kFound = design.type_kinds.find(key);
  if (kFound == design.type_kinds.end()) return kVpiReg;
  return VpiDataTypeVariableKind(kFound->second);
}

}  // namespace

int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name) {
  return NamedTypeKind(design, NamesClass(design, mod.class_decls, name), name);
}

std::vector<ClassDecl*> VpiPackageClasses(const PackageDecl& package) {
  std::vector<ClassDecl*> classes;
  for (const ModuleItem* item : package.items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      classes.push_back(item->class_decl);
    }
  }
  return classes;
}

int VpiPackageNamedTypeVariableKind(const RtlirDesign& design,
                                    const PackageDecl* package,
                                    std::string_view name) {
  if (package == nullptr) {
    return NamedTypeKind(design, NamesClass(design, {}, name), name);
  }
  return NamedTypeKind(design,
                       NamesClass(design, VpiPackageClasses(*package), name),
                       std::string(package->name) + "::" + std::string(name));
}

int VpiScopedTypeVariableKind(const RtlirDesign& design,
                              std::string_view package, const DataType& type) {
  const std::string_view kScope =
      type.scope_name.empty() ? package : type.scope_name;
  const auto kNamed =
      std::ranges::find(design.packages, kScope, &PackageDecl::name);
  return VpiPackageNamedTypeVariableKind(
      design, kNamed == design.packages.end() ? nullptr : *kNamed,
      type.type_name);
}

namespace {

struct MemberSite {
  const RtlirDesign* design;
  const RtlirModule* mod;
  const std::string& prefix;
  const VpiObjectMap& objects;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

int NamedFieldKind(const MemberSite& site, std::string_view name) {
  if (site.mod == nullptr) {
    return VpiDataTypeVariableKind(site.ctx.FindTypeKind(name));
  }
  return VpiNamedTypeVariableKind(*site.design, *site.mod, name);
}

VpiObject* MakeMember(VpiObject* holder, const StructFieldInfo& field,
                      const MemberSite& site) {
  const VpiAttachBuild& build = site.build;
  VpiObject* member = build.alloc();
  const bool kOfNet =
      holder->type == vpiStructNet || holder->type == vpiUnionNet;
  if (kOfNet && field.nested != nullptr) {
    member->type = field.nested->is_union ? vpiUnionNet : vpiStructNet;
    member->packed = field.nested->is_packed;
  } else if (kOfNet) {
    member->type = kVpiNet;
  } else if (field.type_kind == DataTypeKind::kNamed) {
    member->type = NamedFieldKind(site, field.type_name);
  } else {
    member->type = VpiDataTypeVariableKind(field.type_kind);
  }
  member->parent = holder;
  member->name = build.keep(std::string(field.name));
  member->full_name = holder->full_name + "." + std::string(field.name);
  member->decl_signed = field.is_signed;
  VpiScalarVectorQuery shape;
  shape.var_type = member->type;
  shape.has_packed_dimension = field.width > 1;
  member->decl_scalar = VpiVariableScalar(shape);
  member->decl_vector = VpiVariableVector(shape);
  auto* storage = build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(build.arena, field.width);
  storage->value.is_signed = field.is_signed;
  storage->value.is_real =
      member->type == vpiRealVar || member->type == vpiShortRealVar;
  if (field.nested != nullptr) {
    storage->is_4state = HasFourStateMember(*field.nested);
  }
  member->var = storage;
  member->size = static_cast<int>(field.width);
  member->member_of = holder;
  member->member_offset = field.bit_offset;
  holder->children.push_back(member);
  return member;
}

std::optional<PackedDims> MemberBitDims(const VpiObject& member,
                                        const StructFieldInfo& field) {
  const bool kVector = member.type == kVpiReg || member.type == vpiBitVar;
  const bool kPacked = field.nested != nullptr && field.nested->is_packed;
  if (!VpiIsVariablesType(member.type) || field.width <= 1 ||
      field.unpacked_dims != nullptr || field.is_dynamic ||
      (!kVector && !kPacked)) {
    return std::nullopt;
  }
  if (kVector && field.packed_elem_width > 1) {
    return PackedDims{PackedRange{field.packed_left, field.packed_right},
                      PackedRange::Implicit(field.packed_elem_width)};
  }
  if (kVector && field.decl_range) return PackedDims{*field.decl_range};
  return PackedDims{PackedRange::Implicit(field.width)};
}

struct MemberArrayShape {
  std::vector<PackedRange> dims;
  int element_type = 0;
  uint32_t element_width = 0;
  uint32_t count = 1;
  VpiObject* root = nullptr;
  uint32_t offset = 0;
  const VpiAttachBuild* build = nullptr;
};

void MakeMemberLevel(VpiObject* level, const MemberArrayShape& shape,
                     std::size_t depth, const std::vector<int64_t>& outer,
                     uint32_t& position) {
  const VpiAttachBuild& build = *shape.build;
  const PackedRange& dim = shape.dims[depth];
  const bool kInnermost = depth + 1 == shape.dims.size();
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  std::vector<int>& indices = level->array_dim_indices.emplace_back();
  for (int64_t index = dim.left;; index += kStep) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    VpiObject* element = build.alloc();
    element->parent = level;
    element->name = build.keep(std::string(level->name) + kSuffix);
    element->full_name = level->full_name + kSuffix;
    element->array_member = true;
    element->index = static_cast<int>(index);
    element->index_expr = VpiIntConstant(index, build);
    element->children.push_back(element->index_expr);
    for (int64_t outer_index : outer) {
      element->children.push_back(VpiIntConstant(outer_index, build));
    }
    if (kInnermost) {
      element->type = shape.element_type;
      element->decl_signed = level->decl_signed;
      element->decl_scalar = level->decl_scalar;
      element->decl_vector = level->decl_vector;
      auto* storage = build.arena.Create<Variable>();
      storage->value = MakeLogic4Vec(build.arena, shape.element_width);
      storage->value.is_signed = level->decl_signed;
      element->var = storage;
      element->size = static_cast<int>(shape.element_width);
      element->member_of = shape.root;
      element->member_offset =
          shape.offset + ((shape.count - 1 - position++) * shape.element_width);
    } else {
      element->type = vpiArrayVar;
      element->array_type = vpiStaticArray;
      element->size = static_cast<int>(shape.dims[depth + 1].HighIndex() -
                                       shape.dims[depth + 1].LowIndex() + 1);
      element->decl_scalar = level->decl_scalar;
      element->decl_vector = level->decl_vector;
      element->decl_signed = level->decl_signed;
      std::vector<int64_t> inner{index};
      inner.insert(inner.end(), outer.begin(), outer.end());
      MakeMemberLevel(element, shape, depth + 1, inner, position);
    }
    level->children.push_back(element);
    indices.push_back(static_cast<int>(index));
    if (index == dim.right) break;
  }
}

void MakeMemberElements(VpiObject* array, const StructFieldInfo& field,
                        std::vector<PackedRange> dims,
                        const VpiAttachBuild& build) {
  MemberArrayShape shape;
  shape.dims = std::move(dims);
  for (const PackedRange& dim : shape.dims) {
    shape.count *= static_cast<uint32_t>(dim.HighIndex() - dim.LowIndex() + 1);
  }
  shape.element_type = array->type;
  shape.element_width = field.width / shape.count;
  shape.root = array->member_of;
  shape.offset = array->member_offset;
  shape.build = &build;
  VpiScalarVectorQuery element;
  element.var_type = shape.element_type;
  element.has_packed_dimension = shape.element_width > 1;
  array->decl_scalar = VpiVariableScalar(element);
  array->decl_vector = VpiVariableVector(element);
  array->type = vpiArrayVar;
  array->array_type = vpiStaticArray;
  array->size = static_cast<int>(shape.dims.front().HighIndex() -
                                 shape.dims.front().LowIndex() + 1);
  uint32_t position = 0;
  MakeMemberLevel(array, shape, 0, {}, position);
}

std::vector<PackedRange> MemberUnpackedDims(const StructFieldInfo& field,
                                            SimContext& ctx) {
  std::vector<PackedRange> dims;
  if (field.unpacked_dims == nullptr || field.is_dynamic) return dims;
  for (const Expr* dim : *field.unpacked_dims) {
    std::optional<PackedRange> range = WrittenUnpackedDim(dim, ctx);
    if (!range) return {};
    dims.push_back(*range);
  }
  return dims;
}

void MakeMembers(VpiObject* holder, const StructTypeInfo& info,
                 const MemberSite& site) {
  for (const StructFieldInfo& field : info.fields) {
    VpiObject* member = MakeMember(holder, field, site);
    if (holder->member_of != nullptr) {
      member->member_of = holder->member_of;
      member->member_offset += holder->member_offset;
    }
    std::vector<PackedRange> dims = MemberUnpackedDims(field, site.ctx);
    if (!dims.empty() && VpiIsVariablesType(member->type)) {
      MakeMemberElements(member, field, std::move(dims), site.build);
    } else if (field.nested != nullptr) {
      MakeMembers(member, *field.nested, site);
    }
    if (const std::optional<PackedDims> kDims = MemberBitDims(*member, field)) {
      VpiMakeMemberBits(*member, *kDims, site.build);
    }
  }
}

void MakeElementMembers(VpiObject* array, const StructTypeInfo& info,
                        const MemberSite& site) {
  for (VpiObject* element : array->children) {
    if (!element->array_member) continue;
    if (VpiIsArrayVarType(element->type)) {
      MakeElementMembers(element, info, site);
    } else if (element->var != nullptr) {
      element->type = info.is_union ? vpiUnionVar : vpiStructVar;
      element->packed = info.is_packed;
      MakeMembers(element, info, site);
    }
  }
}

void AttachVariableMembers(const MemberSite& site) {
  for (const RtlirVariable& var : site.mod->variables) {
    const std::string kKey = VpiFlatName(site.prefix, var.name);
    VpiObject* holder = FindObjectForFlatName(site.objects, kKey);
    const StructTypeInfo* info = site.ctx.GetVariableStructType(kKey);
    if (holder == nullptr || info == nullptr) continue;
    if (VpiIsArrayVarType(holder->type)) {
      MakeElementMembers(holder, *info, site);
    } else if (holder->var != nullptr &&
               (holder->type == vpiStructVar || holder->type == vpiUnionVar)) {
      MakeMembers(holder, *info, site);
    }
  }
}

void AttachNetMembers(const MemberSite& site) {
  for (const RtlirNet& net : site.mod->nets) {
    const std::string kKey = VpiFlatName(site.prefix, net.name);
    const StructTypeInfo* info = site.ctx.GetVariableStructType(kKey);
    if (info == nullptr || VpiNetObjectKind(net) == vpiPackedArrayNet) continue;
    VpiObject* holder = FindObjectForFlatName(site.objects, kKey);
    holder->type = info->is_union ? vpiUnionNet : vpiStructNet;
    holder->packed = info->is_packed;
    if (info->is_union && net.dtype != nullptr) {
      holder->tagged = net.dtype->is_tagged;
      holder->soft = net.dtype->is_soft;
    }
    MakeMembers(holder, *info, site);
  }
}

const StructTypeInfo* InlineElementLayout(const DataType& written,
                                          SimContext& ctx) {
  DataType element = written;
  element.packed_dim_left = nullptr;
  element.packed_dim_right = nullptr;
  element.extra_packed_dims.clear();
  Arena& arena = ctx.GetArena();
  auto* key = arena.Create<std::string>(
      std::format("[]@{:x}", reinterpret_cast<uintptr_t>(&written)));
  RegisterAggregateLayout(*key, &written, EvalTypeWidth(element), ctx, arena);
  return ctx.FindStructType(*key);
}

const StructTypeInfo* PackedArrayElementLayout(const DataType* written,
                                               SimContext& ctx) {
  if (written == nullptr) return nullptr;
  if (!written->struct_members.empty()) {
    return InlineElementLayout(*written, ctx);
  }
  if (written->scope_name.empty())
    return ctx.FindStructType(written->type_name);
  return ctx.FindStructType(std::string(written->scope_name) +
                            "::" + std::string(written->type_name));
}

void RootMembersAt(VpiObject& holder, const VpiObject& sub, VpiObject& top) {
  for (VpiObject* member : holder.children) {
    if (member->member_of != &sub) continue;
    member->member_of = &top;
    member->member_offset += static_cast<uint32_t>(sub.bit_offset);
    RootMembersAt(*member, sub, top);
  }
}

void MakeSubelementMembers(VpiObject& holder, VpiObject& top,
                           const StructTypeInfo& info, const MemberSite& site) {
  for (VpiObject* sub : holder.children) {
    if (sub->parent != &top) continue;
    if (sub->type == vpiPackedArrayNet || sub->type == vpiPackedArrayVar) {
      MakeSubelementMembers(*sub, top, info, site);
    } else if (sub->type == vpiStructNet || sub->type == vpiUnionNet ||
               sub->type == vpiStructVar || sub->type == vpiUnionVar) {
      MakeMembers(sub, info, site);
      RootMembersAt(*sub, *sub, top);
    }
  }
}

void MakePackedArrayMembers(VpiObject* top, const DataType* written,
                            const MemberSite& site) {
  if (top == nullptr ||
      (top->type != vpiPackedArrayNet && top->type != vpiPackedArrayVar)) {
    return;
  }
  const StructTypeInfo* info = PackedArrayElementLayout(written, site.ctx);
  if (info != nullptr) MakeSubelementMembers(*top, *top, *info, site);
}

}  // namespace

void VpiMakeLocalMembers(VpiObject* local, const StructTypeInfo& layout,
                         SimContext& ctx, const VpiAttachBuild& build) {
  const std::string kNoPrefix;
  const VpiObjectMap kNoObjects;
  MakeMembers(local, layout,
              {nullptr, nullptr, kNoPrefix, kNoObjects, ctx, build});
}

void AttachPackedArrayMembers(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const MemberSite kSite{design, mod, prefix, objects, ctx, build};
        for (const RtlirNet& net : mod->nets) {
          MakePackedArrayMembers(
              FindObjectForFlatName(objects, VpiFlatName(prefix, net.name)),
              net.written_type, kSite);
        }
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          MakePackedArrayMembers(
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name)),
              var.written_type, kSite);
        }
      });
}

int VpiNetObjectKind(const RtlirNet& net) {
  if (VpiNetIsInterconnect(net)) return vpiInterconnectNet;
  switch (net.data_kind) {
    case DataTypeKind::kStruct:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiStructNet;
    case DataTypeKind::kUnion:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiUnionNet;
    case DataTypeKind::kEnum:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiEnumNet;
    case DataTypeKind::kInteger:
      return vpiIntegerNet;
    case DataTypeKind::kTime:
      return vpiTimeNet;
    case DataTypeKind::kBit:
      return vpiBitNet;
    case DataTypeKind::kByte:
      return vpiByteNet;
    case DataTypeKind::kShortint:
      return vpiShortIntNet;
    case DataTypeKind::kInt:
      return vpiIntNet;
    case DataTypeKind::kLongint:
      return vpiLongIntNet;
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return vpiRealNet;
    case DataTypeKind::kShortreal:
      return vpiShortRealNet;
    default:
      return kVpiNet;
  }
}

void RecordNetObjectKinds(const RtlirDesign* design,
                          const VpiObjectMap& objects) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          const int kKind = VpiNetObjectKind(net);
          for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
            VpiObject* obj = FindObjectForFlatName(objects, key);
            if (obj != nullptr && obj->type == kVpiNet) obj->type = kKind;
          }
        }
      });
}

void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build) {
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const MemberSite kSite{design, mod, prefix, objects, ctx, build};
        AttachVariableMembers(kSite);
        AttachNetMembers(kSite);
      });
}

}  // namespace delta
