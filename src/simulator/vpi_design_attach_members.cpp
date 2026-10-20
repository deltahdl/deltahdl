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
    // §6.12 makes realtime a synonym for real.
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
    // §37.27 and §37.29.
    case DataTypeKind::kEvent:
      return vpiNamedEvent;
    case DataTypeKind::kVirtualInterface:
      return vpiVirtualInterfaceVar;
    default:
      return kVpiReg;
  }
}

namespace {

// §8.3, §9.7, §15.3 and §15.4: whether `name` names a class a scope sees:
// one of `classes`, those the scope declares, one the compilation unit
// declares, or one of the built-in classes.
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

// §6.18 with §8.3: the object kind of a variable of a type that is a class
// where `names_class`, and otherwise the one the typedef the design records
// under `key` stands for, a class where its chain of names ends in one.
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

namespace {

// §37.26: the member of `holder` the field `field` lays out: its vpiParent is
// the struct or union var or net, it is named after the field, its kind is a
// net for a net's member and otherwise the one a variable of the field's type
// has (§37.17), and its value is the field's bits of the holder's value, a
// copy that a read refreshes and a write is copied back from, read as a real
// where the field is one.
VpiObject* MakeMember(VpiObject* holder, const StructFieldInfo& field,
                      const RtlirDesign& design, const RtlirModule& mod,
                      const VpiAttachBuild& build) {
  VpiObject* member = build.alloc();
  // §37.16 detail 31: a member of a struct or union net is a net, a struct or
  // union net itself where its field is a structure or union.
  const bool kOfNet =
      holder->type == vpiStructNet || holder->type == vpiUnionNet;
  if (kOfNet && field.nested != nullptr) {
    member->type = field.nested->is_union ? vpiUnionNet : vpiStructNet;
    member->packed = field.nested->is_packed;
  } else if (kOfNet) {
    member->type = kVpiNet;
  } else if (field.type_kind == DataTypeKind::kNamed) {
    member->type = VpiNamedTypeVariableKind(design, mod, field.type_name);
  } else {
    member->type = VpiDataTypeVariableKind(field.type_kind);
  }
  member->parent = holder;
  member->name = build.keep(std::string(field.name));
  member->full_name = holder->full_name + "." + std::string(field.name);
  member->decl_signed = field.is_signed;
  // §37.17 detail 20: a member is a scalar or a vector as a variable of its
  // field's type is, a bit or logic field wider than one bit having a packed
  // dimension; one declared as an unpacked array answers as its element
  // (MakeMemberElements).
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
  member->var = storage;
  member->size = static_cast<int>(field.width);
  member->member_of = holder;
  member->member_offset = field.bit_offset;
  holder->children.push_back(member);
  return member;
}

// §37.17 detail 12 with §7.4.1: the dimensions the bits of `member`, of the
// field `field`, are indexed by: a bit or logic member's packed ones, the
// outermost as the layout records it over its elements' own [n-1:0], and a
// packed structure's or union's implicit [n-1:0] (§7.2.1). None for a net's
// member, a member of one bit, an unpacked array or dynamic member, or one of
// any other type.
std::optional<PackedDims> MemberBitDims(const VpiObject& member,
                                        const StructFieldInfo& field) {
  const bool kVector = member.type == kVpiReg || member.type == vpiBitVar;
  const bool kPacked = field.nested != nullptr && field.nested->is_packed;
  if (!VpiIsVariablesType(member.type) || field.width <= 1 ||
      field.unpacked_dims != nullptr || field.is_dynamic ||
      (!kVector && !kPacked)) {
    return std::nullopt;
  }
  if (kVector && field.packed_elem_width != 0) {
    return PackedDims{PackedRange{field.packed_left, field.packed_right},
                      PackedRange::Implicit(field.packed_elem_width)};
  }
  // §7.4.1: a member of one packed dimension indexes its bits as its
  // declaration does, `reg [0:7] b`'s b[7] being its least significant bit.
  if (kVector && field.decl_range) return PackedDims{*field.decl_range};
  return PackedDims{PackedRange::Implicit(field.width)};
}

// What the elements of a member declared with unpacked dimensions are made
// of: its dimensions, outermost first, the kind and width of one element, the
// number of elements, the outermost structure whose storage the elements read
// their bits of, at the member's offset there, and what a run builds with.
struct MemberArrayShape {
  std::vector<PackedRange> dims;
  int element_type = 0;
  uint32_t element_width = 0;
  uint32_t count = 1;
  VpiObject* root = nullptr;
  uint32_t offset = 0;
  const VpiAttachBuild* build = nullptr;
};

// §37.17 details 2, 18 and 26: the members of `level`, the array var or
// subarray of the member `shape` describes at dimension `depth`: one per
// index, left index first, carrying its index and those `outer` that select
// `level`, innermost first. At the last dimension each is a variable of the
// member's type holding its bits of the outermost structure, where the layout
// puts the element written first in the most significant ones; at every other
// it is a subarray, an array var of its own. `position` counts the elements
// made so far.
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

// §37.17 details 2, 18 and 26: the member `array` of the field `field`,
// declared with the unpacked dimensions `dims`, made the array var it is,
// with its subarrays and elements (MakeMemberLevel).
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
  // §37.17 detail 20: an array var answers vpiScalar and vpiVector as its
  // element does.
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

// §7.4.2: the unpacked dimensions the member of the field `field` writes,
// each evaluated in the scope `ctx` has set; none where it writes none or
// where one is not a fixed range or size.
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

// What the members of one instance are made from: its module, the objects
// keyed under its name `prefix`, and what a run builds with.
struct MemberSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const VpiObjectMap& objects;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// The member per field of the layout `info` gives `holder`. §37.17 detail 28's
// example names `str1.inner1.j1`: a member of a structure or union type has a
// member per field of its own, each read from and written back to the storage
// of the outermost structure, at its offset there, as each member's bits are
// (detail 12).
void MakeMembers(VpiObject* holder, const StructTypeInfo& info,
                 const MemberSite& site) {
  for (const StructFieldInfo& field : info.fields) {
    VpiObject* member =
        MakeMember(holder, field, site.design, site.mod, site.build);
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

// §37.17 detail 26: an element of an array of structures or unions is a
// struct or union var of its own, `spa[9][12]`, with a member per field of
// the array's layout, each reached through the element. The leaves of the
// array the elements pass made are those elements.
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

// §37.17 details 3, 17 and 26: a struct or union var, packed or not, has a
// member variable per field, the struct as its vpiParent and the field's value
// as its own. The run keeps the whole struct as one variable, and no member
// object was made, so vpiMember reached nothing and no name reached a field; a
// packed one was passed over after that, though §37.26 makes vpiPacked only a
// property of the struct var.
void AttachVariableMembers(const MemberSite& site) {
  for (const RtlirVariable& var : site.mod.variables) {
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

// §37.26: a net of a structure or union type is a struct net or a union net,
// with a member net per field. Every net of the run is an object
// (VpiContext::Attach), and the run registers the layout of each one of an
// aggregate type under the same key (RegisterAggregateLayout); each reported
// vpiNet and held no member.
void AttachNetMembers(const MemberSite& site) {
  for (const RtlirNet& net : site.mod.nets) {
    const std::string kKey = VpiFlatName(site.prefix, net.name);
    const StructTypeInfo* info = site.ctx.GetVariableStructType(kKey);
    // §37.16 detail 1: a packed array net of a structure written in place has
    // the whole array's layout under its name, but its members belong to its
    // subelements (AttachPackedArrayMembers).
    if (info == nullptr || VpiNetObjectKind(net) == vpiPackedArrayNet) continue;
    VpiObject* holder = FindObjectForFlatName(site.objects, kKey);
    holder->type = info->is_union ? vpiUnionNet : vpiStructNet;
    // §37.16 detail 24: whether it is packed, which decides its vpiSize.
    holder->packed = info->is_packed;
    // §37.26: whether the union was declared tagged or soft.
    if (info->is_union && net.dtype != nullptr) {
      holder->tagged = net.dtype->is_tagged;
      holder->soft = net.dtype->is_soft;
    }
    MakeMembers(holder, *info, site);
  }
}

// §7.2.1: the layout of one element of a packed array of the structure or
// union `written` writes in place, which no typedef registers. It is built
// from the fields written as RegisterAggregateLayout builds a declaration's,
// as wide as the type without the array's packed dimensions, under a key
// naming the written type, which stands at one address for the run.
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

// §37.16 detail 32 and §37.18 detail 3 with §6.18: the layout of the struct
// or union each subelement of a packed array declared with the type `written`
// holds past its last packed dimension: that of a structure or union written
// in place, or of the typedef it names, which the design's layouts key by its
// package or class where one is written (§26.3); null for an enum.
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

// The members under `holder` that MakeMembers rooted at the net subelement
// `sub`, rooted instead at the packed array net `top` holding the run's
// storage, at the subelement's offset in it. A var subelement is rooted at
// its packed array var already, and so are the members made under it.
void RootMembersAt(VpiObject& holder, const VpiObject& sub, VpiObject& top) {
  for (VpiObject* member : holder.children) {
    if (member->member_of != &sub) continue;
    member->member_of = &top;
    member->member_offset += static_cast<uint32_t>(sub.bit_offset);
    RootMembersAt(*member, sub, top);
  }
}

// §37.16 detail 32, §37.18 detail 3 and §37.26: each struct or union
// subelement under `holder`, the packed array `top` or a subelement of it,
// given a member per field of `info`, each holding its field's bits of the
// subelement's share of `top`.
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

// The members of the subelements of the packed array `top`, if it is one,
// declared with the type `written`.
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

void AttachPackedArrayMembers(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const MemberSite kSite{*design, *mod, prefix, objects, ctx, build};
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
  // §37.24 (figure): a generic interconnect is an interconnect net, which has
  // no data type of its own, whatever net a port connection merged it into.
  if (VpiNetIsInterconnect(net)) return vpiInterconnectNet;
  switch (net.data_kind) {
    // §37.16 detail 1: a packed struct, union or enum net with a packed
    // dimension of its own is a packed array net.
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
    // §6.7.1 keeps a 2-state or real type off a built-in net type, so these
    // arise through a user-defined nettype (§6.6.7), the figure's user
    // defined net.
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
  // §37.16 (figure): a net is drawn as the kind its data type makes it. The run
  // made every net a logic net, and only a struct or union net with a layout
  // of its own was told otherwise (AttachNetMembers), so no design had an enum
  // net, an integer net or a packed array net.
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
        const MemberSite kSite{*design, *mod, prefix, objects, ctx, build};
        AttachVariableMembers(kSite);
        AttachNetMembers(kSite);
      });
}

}  // namespace delta
