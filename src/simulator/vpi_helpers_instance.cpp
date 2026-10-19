#include <algorithm>
#include <array>
#include <cctype>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <functional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"
#include "simulator/vpi_user.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_delay_devices.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_source_delay.h"

namespace delta {

VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
  // §38.27: a file vpi_mcd_open opened and nothing closed is closed with the
  // tool, its text written out.
  for (auto& entry : channels_.mcd_files) std::fclose(entry.second);
}

VpiHandle VpiContext::AllocObject() {
  auto* obj = new VpiObject();
  all_objects_.push_back(obj);
  return obj;
}

// §37.3.7: derive the reported allocation scheme from how the object was
// allocated. Frame/thread allocations are Automatic, dynamic-memory (class)
// allocations are Dynamic, and everything else falls through to the mandated
// Other default.
int VpiAllocSchemeFor(VpiAllocKind kind) {
  switch (kind) {
    case VpiAllocKind::kFrameOrThread:
      return kVpiAutomaticScheme;
    case VpiAllocKind::kDynamic:
      return kVpiDynamicScheme;
    default:
      // VpiAllocKind::kOther, the one kind left.
      return kVpiOtherScheme;
  }
}

// §37.10 details 1 and 10: keep only the entries that are user-defined and
// explicitly declared in the instance, in their original order. Built-in
// definitions and entries merely made visible (e.g. by import) are dropped.
static std::vector<const VpiTypeDeclEntry*> FilterDeclaredUserEntries(
    const std::vector<VpiTypeDeclEntry>& entries) {
  std::vector<const VpiTypeDeclEntry*> visible;
  for (const auto& entry : entries) {
    if (entry.user_defined && entry.declared_in_instance) {
      visible.push_back(&entry);
    }
  }
  return visible;
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

bool VpiIsInstanceType(int type) {
  // §37.10 detail 3: an instance is a package, module, interface, or program.
  return type == kVpiModule || type == vpiPackage || type == vpiInterface ||
         type == vpiProgram;
}

void VpiCollectInstanceAssertions(VpiHandle scope, VpiHandle iter) {
  // §39.3.1 step b: the assertions of an instance are iterated by passing
  // vpi_iterate() the instance's handle as the reference. All of them is what
  // the step asks for, and an assertion is written wherever the
  // instance body admits one - directly, inside a begin block, inside a
  // procedure, inside a generate scope - so the walk descends through the
  // scopes the body holds rather than reading off its immediate children.
  for (VpiObject* child : scope->children) {
    if (VpiIsAssertionType(child->type)) iter->children.push_back(child);
    // An assertion inside a nested instance is an assertion of that instance,
    // which is what its own handle would be passed to reach: the walk stops at
    // the boundary rather than claiming what belongs to the instance below.
    if (VpiIsInstanceType(child->type)) continue;
    VpiCollectInstanceAssertions(child, iter);
  }
}

VpiHandle VpiInstanceOf(VpiHandle obj) {
  // §37.10 detail 3: walk outward to the first enclosing scope that is itself
  // an instance; that is the immediate instance the object is instantiated in.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsInstanceType(scope->type)) return scope;
  }
  return nullptr;
}

VpiHandle VpiScopeNamedClockingBlock(VpiHandle scope, bool global) {
  // §37.5/§37.6/§37.9 (figure): the clocking block a scope named default, or
  // the one it named global. §14.12 lets a scope name one of each among the
  // blocks it declares, so the block carries which it is and the edge reaches
  // the one so marked. Null where the scope named none.
  for (auto* child : scope->children) {
    if (child->type != vpiClockingBlock) continue;
    if (global ? child->global_clocking : child->default_clocking) return child;
  }
  return nullptr;
}

VpiHandle VpiScopeDefaultDisableIff(VpiHandle scope) {
  // §37.5/§37.6/§37.9 (figure): the vpiDefaultDisableIff edge reaches the
  // expr or distribution the scope's default disable iff writes, held apart
  // from its children, among which a parameter is an expression too. Null
  // where the scope is under none.
  return scope->disable_condition;
}

VpiHandle VpiInstanceArrayOf(VpiHandle element, int type) {
  // An element keeps its place in the scope around it, which holds the array
  // too (VpiAddArrayElement), so the array is the one of the scope's children
  // holding the element.
  if (!element->array_member) return nullptr;
  for (VpiObject* array : element->parent->children) {
    // §37.11: a primitive reaches the primitive array it belongs to as a
    // module reaches its module array, and either reaches it as an instance
    // array, the class both kinds are of.
    bool kind = VpiIsInstanceArrayType(array->type);
    if (type == vpiModuleArray) kind = array->type == vpiModuleArray;
    if (type == vpiPrimitiveArray) kind = VpiIsPrimitiveArrayType(array->type);
    if (kind &&
        std::ranges::find(array->children, element) != array->children.end()) {
      return array;
    }
  }
  return nullptr;
}

namespace {

// §37.11 with §38.20: the element of the instance array `array` that
// `indices` names, one per dimension of the array, leftmost first; null for
// none.
VpiHandle InstanceArrayElementAt(const VpiObject& array,
                                 std::span<const int> indices) {
  for (VpiObject* child : array.children) {
    if (child->array_member &&
        std::ranges::equal(child->instance_facts.array_indices, indices)) {
      return child;
    }
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiSubobjectByIndices(VpiHandle parent,
                                std::span<const int> indices) {
  if (VpiIsInstanceArrayType(parent->type)) {
    return InstanceArrayElementAt(*parent, indices);
  }
  // §38.20: apply the indices in the order provided - leftmost first -
  // following the array dimension declaration from the leftmost to the
  // rightmost range of the reference handle, with an optional trailing
  // bit-select index. Each step descends to the subobject carrying that index.
  // If any index names no subobject the chain is not a legal SystemVerilog
  // index select expression, so the result is a null handle.
  VpiHandle current = parent;
  for (const int kIndex : indices) {
    VpiHandle next = nullptr;
    for (auto* child : current->children) {
      if (VpiIndexSelects(*child, kIndex)) {
        next = child;
        break;
      }
    }
    if (!next) return nullptr;
    current = next;
  }
  return current;
}

VpiHandle VpiModuleOf(VpiHandle obj) {
  // §37.10 detail 2: report the nearest enclosing module, or null when no
  // module encloses the object.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (scope->type == kVpiModule) return scope;
  }
  return nullptr;
}

int VpiMemoryIterationItemType() {
  // §37.10 detail 4: the iteration yields array variable objects, never the
  // legacy vpiMemory object kind.
  return vpiRegArray;
}

std::string VpiCompilationUnitFullName(std::string_view object_path) {
  // §37.10 detail 5: such names begin with the "$unit::" scope name.
  return "$unit::" + std::string(object_path);
}

std::string VpiPackageFullName(std::string_view package_name) {
  // §37.10 detail 5: a package's full name is its own name ending in "::".
  return std::string(package_name) + "::";
}

std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path) {
  // §37.10 detail 5: package name, the "::" separator, then the member path.
  return std::string(package_name) + "::" + std::string(member_path);
}

std::string_view VpiNameSeparator(bool package_or_class_defn_boundary) {
  // §37.10 detail 5: "::" follows a package or class-definition scope; "." is
  // used in every other case.
  return package_or_class_defn_boundary ? "::" : ".";
}

bool VpiHandleByNameAccessible(const VpiObject& obj) {
  // §37.10 detail 6: imported items and compilation-unit objects are not
  // reachable through vpi_handle_by_name().
  return !obj.imported && !obj.in_compilation_unit;
}

int VpiSmallestTimePrecision(const std::vector<int>& precisions) {
  // §37.10 detail 7: the smallest (finest) precision wins; nothing to report
  // when the design has no modules.
  if (precisions.empty()) return 0;
  int smallest = precisions.front();
  for (int precision : precisions) {
    if (precision < smallest) smallest = precision;
  }
  return smallest;
}

// ===========================================================================
// §37.36 UDP.
// ===========================================================================

// The primitives the compilation unit of `design` defines, one no instance
// uses among them; an extern prototype names the primitive its definition
// declares (§3.13), so it is none of them.
static std::vector<const UdpDecl*> UnitUdpDefinitions(
    const RtlirDesign& design) {
  std::vector<const UdpDecl*> decls;
  if (design.compilation_unit == nullptr) return decls;
  for (const UdpDecl* decl : design.compilation_unit->udps) {
    if (!decl->is_extern) decls.push_back(decl);
  }
  return decls;
}

std::vector<const UdpDecl*> VpiDesignUdpDecls(const RtlirDesign* design) {
  if (design == nullptr) return {};
  std::vector<const UdpDecl*> decls = UnitUdpDefinitions(*design);

  std::vector<const RtlirModule*> work(design->top_modules.begin(),
                                       design->top_modules.end());
  while (!work.empty()) {
    const RtlirModule* mod = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    for (const auto& child : mod->children) work.push_back(child.resolved);
    for (const RtlirUdpInst& inst : mod->udp_insts) {
      if (inst.decl == nullptr) continue;
      if (std::find(decls.begin(), decls.end(), inst.decl) == decls.end()) {
        decls.push_back(inst.decl);
      }
    }
  }
  return decls;
}

void VpiFillUdpDefnObject(VpiObject* obj, const UdpDecl& decl,
                          std::deque<std::string>& names) {
  obj->type = vpiUdpDefn;
  names.emplace_back(decl.name);
  obj->name = names.back();
  obj->def_name = std::string(decl.name);
  obj->size = static_cast<int>(decl.input_names.size());
  // §37.36 detail 2: vpiPrimType is vpiSeqPrim for a sequential UDP and
  // vpiCombPrim for a combinational one.
  obj->prim_type = decl.is_sequential ? vpiSeqPrim : vpiCombPrim;
}

// §37.36 detail 1: `row` as the table writes it, its input symbols with an
// edge in parentheses among them, then the current state of a sequential row
// and the output, each field set off by a colon.
static std::string DecompiledUdpRow(const UdpTableRow& row) {
  std::string text;
  for (std::size_t i = 0; i < row.inputs.size(); ++i) {
    if (i > 0) text += ' ';
    if (row.inputs[i] != '\x01') {
      text += row.inputs[i];
      continue;
    }
    text += '(';
    text += row.paren_edges[i].first;
    text += row.paren_edges[i].second;
    text += ')';
  }
  if (row.current_state != 0) {
    text += " : ";
    text += row.current_state;
  }
  text += " : ";
  text += row.output;
  return text;
}

VpiObject* VpiUdpInitialStatement(const UdpDecl& decl, VpiObject* initial,
                                  const std::function<VpiObject*()>& alloc,
                                  std::deque<std::string>& names,
                                  Arena& arena) {
  VpiObject* assign = alloc();
  assign->type = vpiAssignment;
  assign->blocking = true;
  assign->parent = initial;
  VpiObject* lhs = alloc();
  lhs->type = kVpiReg;
  names.emplace_back(decl.output_name);
  lhs->name = names.back();
  lhs->size = 1;
  lhs->parent = assign;
  VpiObject* rhs = alloc();
  rhs->type = vpiConstant;
  rhs->const_type = vpiBinaryConst;
  rhs->size = 1;
  rhs->parent = assign;
  auto* bit = arena.Create<Variable>();
  const char kBit = decl.initial_value;
  bit->value = kBit == '0' || kBit == '1'
                   ? MakeLogic4VecVal(arena, 1, kBit == '1' ? 1 : 0)
                   : MakeAllX(arena, 1);
  rhs->var = bit;
  assign->lhs = lhs;
  assign->rhs = rhs;
  return assign;
}

void VpiFillUdpTableEntryObject(VpiObject* obj, const UdpTableRow& row,
                                VpiObject* defn, Arena& arena) {
  obj->type = vpiTableEntry;
  // The symbol entries of a row are the input symbols it matches on, the
  // current state a sequential row carries, and the output symbol it names.
  obj->size = static_cast<int>(row.inputs.size()) +
              (row.current_state != 0 ? 1 : 0) + 1;
  // §37.36 detail 1: the row's text, which a string value reads as it is and
  // a vector value as the ASCII codes of its characters.
  auto* text = arena.Create<Variable>();
  text->value = StringToLogic4Vec(arena, DecompiledUdpRow(row));
  obj->var = text;
  obj->parent = defn;
  defn->children.push_back(obj);
}

// ===========================================================================
// §38.10 the design's module path delays, and §37.40 its timing checks. Both
// are built out of the run's SpecifyManager, which is where a specify block
// reaches the simulation.
// ===========================================================================

// The flat name of the module a specify entry belongs to: its instance prefix
// without the separator it ends in, or, for the empty prefix the first top
// module lowers under, that top's name. Empty where no top was
// lowered, which leaves the entry no module object to stand under.
static std::string_view SpecifyEntryScope(std::string_view inst_prefix,
                                          std::string_view first_top) {
  if (inst_prefix.empty()) return first_top;
  inst_prefix.remove_suffix(1);
  return inst_prefix;
}

// §30.4: the net a module path's output terminal `dst_port` names in the
// module `module` declaring the path, or null where it names a variable or
// nothing the module holds, there being then no net for a delay device to sit
// on.
static VpiHandle ModulePathOutputNet(VpiHandle module,
                                     std::string_view dst_port) {
  for (VpiHandle child : module->children) {
    if (VpiIsNetsType(child->type) && child->name == dst_port) return child;
  }
  return nullptr;
}

// §37.39 and §37.40 (figures): the vpiEdge a path or tchk term reports - the
// edge identifier its path or timing check event was written with (§30.4.2,
// §31.5), `edge` being either edge, and none where it was written without one.
static int VpiEventEdgeOf(SpecifyEdge edge) {
  switch (edge) {
    case SpecifyEdge::kPosedge:
      return vpiPosedge;
    case SpecifyEdge::kNegedge:
      return vpiNegedge;
    case SpecifyEdge::kEdge:
      return vpiAnyEdge;
    default:
      return vpiNoEdge;
  }
}

// A.7.3 with A.7.5.2: the expression a path's or timing check's terminal
// stands for - the signal it names, a member of the interface port it names
// it through where it names one, selected as the terminal was written.
static const Expr* TerminalExpression(const SpecifyTerminal& terminal,
                                      Arena& arena) {
  auto* signal = arena.Create<Expr>();
  signal->kind = ExprKind::kIdentifier;
  signal->text = terminal.name;
  if (!terminal.interface_name.empty()) {
    auto* port = arena.Create<Expr>();
    port->kind = ExprKind::kIdentifier;
    port->text = terminal.interface_name;
    auto* member = arena.Create<Expr>();
    member->kind = ExprKind::kMemberAccess;
    member->lhs = port;
    member->rhs = signal;
    signal = member;
  }
  if (terminal.range_kind == SpecifyRangeKind::kNone) return signal;
  auto* select = arena.Create<Expr>();
  select->kind = ExprKind::kSelect;
  select->base = signal;
  select->index = terminal.range_left;
  if (terminal.range_kind != SpecifyRangeKind::kBitSelect) {
    select->index_end = terminal.range_right;
  }
  select->is_part_select_plus =
      terminal.range_kind == SpecifyRangeKind::kPlusIndexed;
  select->is_part_select_minus =
      terminal.range_kind == SpecifyRangeKind::kMinusIndexed;
  return select;
}

// The object an expression a specify block writes stands for in the instance
// declaring it.
using WrittenExpression = std::function<VpiObject*(const Expr*)>;

// The expressions a specify entry of the instance at `inst_prefix` writes, as
// VpiInstanceExpression makes them, the names resolving in that instance:
// keyed under its prefix without the closing `.`, and the first top's under
// none.
static WrittenExpression ExpressionsIn(std::string_view inst_prefix,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build) {
  return [prefix = std::string(SpecifyEntryScope(inst_prefix, "")), &objects,
          &ctx, &build](const Expr* expr) {
    return VpiInstanceExpression(expr, objects, prefix, ctx, build);
  };
}

// §37.39 (figure): a path term of the module path `path`, reporting the
// direction `direction` and the edge `edge`, standing for the terminal
// written as `expr`.
static VpiObject* AddPathTerm(VpiObject* path, int direction, int edge,
                              VpiObject* expr, const VpiAttachBuild& build) {
  VpiObject* term = build.alloc();
  term->type = vpiPathTerm;
  term->direction = direction;
  term->edge = edge;
  term->term_expr = expr;
  term->parent = path;
  path->children.push_back(term);
  return term;
}

// §30.4.5: the polarity a polarity operator gives a path, as vpiPolarity and
// vpiDataPolarity report it, unknown where none was written.
static int VpiPolarityOf(SpecifyPolarity polarity) {
  switch (polarity) {
    case SpecifyPolarity::kPositive:
      return vpiPositive;
    case SpecifyPolarity::kNegative:
      return vpiNegative;
    default:
      return vpiUnknown;
  }
}

// §37.39 (figure): what the declaration of `path` wrote it as - a parallel or
// full connection (§30.4.6), the polarity of its operator and of its data
// source (§30.4.3, §30.4.5), whether it is an ifnone path (§30.4.4.4) and the
// condition it was written under (§30.4.4) - and its terms: the source and
// destination this path joins and an edge-sensitive path's data source, each
// expression as `expr` makes it.
static void FillModPath(VpiObject* obj, const PathDelay& path,
                        const WrittenExpression& expr,
                        const VpiAttachBuild& build) {
  const SpecifyPathDecl& decl = *path.decl;
  obj->path_type =
      decl.path_kind == SpecifyPathKind::kFull ? vpiPathFull : vpiPathParallel;
  obj->polarity = VpiPolarityOf(decl.polarity);
  obj->data_polarity = VpiPolarityOf(decl.dst_polarity);
  obj->mod_path_has_if_none = decl.is_ifnone;
  obj->written_condition = expr(decl.condition);
  if (path.src_index < decl.src_ports.size()) {
    AddPathTerm(
        obj, vpiInput, VpiEventEdgeOf(decl.edge),
        expr(TerminalExpression(decl.src_ports[path.src_index], build.arena)),
        build);
  }
  if (path.dst_index < decl.dst_ports.size()) {
    AddPathTerm(
        obj, vpiOutput, vpiNoEdge,
        expr(TerminalExpression(decl.dst_ports[path.dst_index], build.arena)),
        build);
  }
  if (decl.data_source != nullptr) {
    AddPathTerm(obj, vpiInput, vpiNoEdge, expr(decl.data_source), build)
        ->data_path_term = true;
  }
}

void VpiContext::AttachModulePathDelays(SimContext& sim_ctx) {
  // §38.10: vpi_get_delays() retrieves an object's delays or pulse limits. A
  // module path is one of the four kinds of
  // object the clause gives legal no_of_delays values for, and it is the one
  // whose twelve transition delays the clause takes without interpreting them
  // -- the 12-value row of Table 38-2 is the path's own array. No object a run
  // built carried a delay at all, so the routine had only what a caller put in
  // an object of its own making to retrieve.
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;
  const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                              VpiPoolKeeper(name_pool_), sim_ctx.GetArena()};

  for (const PathDelay& path : specify->GetPathDelays()) {
    // §30.3 puts a specify block inside a module declaration, so the paths it
    // declares belong to the instance that declared them, or to the first top
    // module where the prefix is empty.
    std::string_view scope =
        SpecifyEntryScope(path.inst_prefix, sim_ctx.FirstTopModule());
    if (scope.empty()) continue;
    // The walk makes any scope it has not met, so a prefix always has one.
    VpiHandle module = DesignObjectForFlatName(scope);

    auto* obj = AllocObject();
    obj->type = vpiModPath;
    obj->parent = module;
    module->children.push_back(obj);  // §37.3.4: the delays the path
                                      // declaration wrote, as vpiDelay reaches
    // them.
    obj->delay_expr =
        VpiSourceDelayExpression(path.source_delays, path.inst_prefix, sim_ctx,
                                 [this] { return AllocObject(); });
    // §37.3.3: where the path declaration was written.
    VpiRecordWrittenLocation(obj, path.loc, sim_ctx);
    // §38.10: the s_vpi_delay array the application allocated holds the delays
    // in the order the SystemVerilog description writes them, which for a
    // module path is the order of its transition slots, and the
    // pulse limits §30.7 gives each of them travel with each delay.
    obj->delays.reserve(path.delay_count);
    for (uint8_t i = 0; i < path.delay_count; ++i) {
      VpiDelayInfo info;
      info.delay = static_cast<double>(path.delays[i]);
      info.min_delay = info.delay;
      info.typ_delay = info.delay;
      info.max_delay = info.delay;
      info.reject = static_cast<double>(path.reject_limit[i]);
      info.min_reject = info.reject;
      info.typ_reject = info.reject;
      info.max_reject = info.reject;
      info.error = static_cast<double>(path.error_limit[i]);
      info.min_error = info.error;
      info.typ_error = info.error;
      info.max_error = info.error;
      obj->delays.push_back(info);
    }
    // §37.45: a module path's delay is one of the three a delay device stands
    // for, and it sits on the net the path's output terminal names.
    VpiPlaceDelayDevice(obj, ModulePathOutputNet(module, path.dst_port), module,
                        vpiModPathDelay, [this] { return AllocObject(); });
    // A path §32's SDF annotation added was declared by no source, so it has
    // nothing written to make.
    if (path.decl != nullptr) {
      FillModPath(obj, path,
                  ExpressionsIn(path.inst_prefix, object_map_, sim_ctx, kBuild),
                  kBuild);
    }
  }
}

// §37.40 (figure): the VPI tchk type each of §31.2's checks reports through
// vpi_get(vpiTchkType).
static int VpiTchkTypeOf(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
      return vpiSetup;
    case TimingCheckKind::kHold:
      return vpiHold;
    case TimingCheckKind::kSetuphold:
      return vpiSetupHold;
    case TimingCheckKind::kRecovery:
      return vpiRecovery;
    case TimingCheckKind::kRemoval:
      return vpiRemoval;
    case TimingCheckKind::kRecrem:
      return vpiRecrem;
    case TimingCheckKind::kWidth:
      return vpiWidth;
    case TimingCheckKind::kPeriod:
      return vpiPeriod;
    case TimingCheckKind::kSkew:
      return vpiSkew;
    case TimingCheckKind::kNochange:
      return vpiNoChange;
    case TimingCheckKind::kTimeskew:
      return vpiTimeskew;
    default:
      // TimingCheckKind::kFullskew, the one kind left.
      return vpiFullskew;
  }
}

// §31.5: one transition an edge_descriptor names, its levels as
// TimingCheckEntry folds them to '0', '1' and 'x', and the vpiEdge bit
// Annex K.2 gives it.
struct VpiEdgeTransition {
  char from;
  char to;
  int bit;
};

constexpr std::array<VpiEdgeTransition, 6> kVpiEdgeTransitions = {{
    {'0', '1', vpiEdge01},
    {'1', '0', vpiEdge10},
    {'0', 'x', vpiEdge0x},
    {'x', '1', vpiEdgex1},
    {'1', 'x', vpiEdge1x},
    {'x', '0', vpiEdgex0},
}};

// §37.40 (figure) with §31.5: the vpiEdge of a timing check event written with
// `edge` and, where it wrote an edge_control_specifier, the transitions
// `descriptors` lists - those transitions alone, one bit each, rather than
// every edge a bare `edge` names.
static int VpiTchkEventEdgeOf(
    SpecifyEdge edge, const std::vector<std::pair<char, char>>& descriptors) {
  if (descriptors.empty()) return VpiEventEdgeOf(edge);
  int mask = vpiNoEdge;
  for (const auto& [from, to] : descriptors) {
    for (const VpiEdgeTransition& transition : kVpiEdgeTransitions) {
      if (transition.from == from && transition.to == to)
        mask |= transition.bit;
    }
  }
  return mask;
}

// §37.40 (figure): one of the check's two event terms - the tchk term the
// vpiTchkRefTerm and vpiTchkDataTerm relations reach. Its own properties are
// the event's: the edge it was written with (vpiEdge) and the signal it names.
static VpiObject* MakeTchkTerm(VpiObject* term, std::string_view signal,
                               int edge, VpiObject* tchk,
                               std::deque<std::string>& names) {
  term->type = vpiTchkTerm;
  names.emplace_back(signal);
  term->name = names.back();
  term->edge = edge;
  term->parent = tchk;
  tchk->children.push_back(term);
  return term;
}

// §31.2: how many timing_check_limits a check of `kind` is written with - two
// for a $setuphold's setup and hold limits, a $recrem's recovery and removal
// limits and a $fullskew's two, none for a $nochange, whose edge offsets are
// no limits (§31.4.6, A.7.5.1), and one for every other check, $width's
// threshold being no limit either (§31.4.4).
static int LimitCountOf(TimingCheckKind kind) {
  if (kind == TimingCheckKind::kNochange) return 0;
  return kind == TimingCheckKind::kSetuphold ||
                 kind == TimingCheckKind::kRecrem ||
                 kind == TimingCheckKind::kFullskew
             ? 2
             : 1;
}

// §37.40 (figure): one limit of the check `tchk`, `ticks` long, which
// vpi_get_delays() retrieves in the order the check wrote its limits.
static void AddTchkLimit(VpiObject* tchk, uint64_t ticks) {
  VpiDelayInfo limit;
  limit.delay = static_cast<double>(ticks);
  limit.min_delay = limit.delay;
  limit.typ_delay = limit.delay;
  limit.max_delay = limit.delay;
  tchk->delays.push_back(limit);
}

// A.7.5.2: the expression a delayed_reference or delayed_data stands for, the
// signal `name` selected by `index` where one was written; none where the
// check names none.
static const Expr* DelayedSignalExpression(std::string_view name, Expr* index,
                                           Arena& arena) {
  if (name.empty()) return nullptr;
  SpecifyTerminal terminal;
  terminal.name = name;
  terminal.range_left = index;
  if (index != nullptr) terminal.range_kind = SpecifyRangeKind::kBitSelect;
  return TerminalExpression(terminal, arena);
}

// §37.40 (figure): the signal the event of `term` names and the `&&&`
// condition it was written with (§31.7), as `expr` makes them.
static void FillTchkTerm(VpiObject* term, const SpecifyTerminal& terminal,
                         const Expr* condition, const WrittenExpression& expr,
                         Arena& arena) {
  if (term == nullptr) return;
  term->term_expr = expr(TerminalExpression(terminal, arena));
  term->written_condition = expr(condition);
}

// §37.40 detail 2: the arguments of the check `tchk` that `decl` declares, in
// the order A.7.5.1 writes them - its events as its tchk terms, $setup naming
// its data event first (§31.3.1), then its limits, the threshold or edge
// offsets written where a limit stands, its notifier, and what the check
// writes behind the notifier - each argument but an event as `expr` makes it.
// An argument the declaration left out has none.
static void FillTchkArguments(VpiObject* tchk, const TimingCheckDecl& decl,
                              const WrittenExpression& expr, Arena& arena) {
  VpiObject* first = tchk->tchk_ref_term;
  VpiObject* second = tchk->tchk_data_term;
  FillTchkTerm(first, decl.ref_terminal, decl.ref_condition, expr, arena);
  FillTchkTerm(second, decl.data_terminal, decl.data_condition, expr, arena);
  if (decl.check_kind == TimingCheckKind::kSetup) std::swap(first, second);
  std::vector<VpiObject*> arguments = {first, second};
  for (const Expr* limit : decl.limits) arguments.push_back(expr(limit));
  arguments.push_back(tchk->tchk_notifier);
  const std::vector<const Expr*> kTrailing = {
      decl.timestamp_cond,
      decl.timecheck_cond,
      DelayedSignalExpression(decl.delayed_ref, decl.delayed_ref_expr, arena),
      DelayedSignalExpression(decl.delayed_data, decl.delayed_data_expr, arena),
      decl.event_based_flag,
      decl.remain_active_flag};
  for (const Expr* trailing : kTrailing) arguments.push_back(expr(trailing));
  std::erase(arguments, nullptr);
  tchk->tchk_arguments = std::move(arguments);
}

void VpiContext::AttachTimingChecks(SimContext& sim_ctx) {
  // §37.40 draws a tchk carrying the kind of check it is (vpiTchkType), the
  // limit vpi_get_delays() retrieves, the two event terms details 1 and 2 are
  // about, and the notifier it toggles. No pass built one, so the whole of the
  // subclause answered for no design: a module's vpiTchk iteration reached
  // none of the checks its specify block declared.
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;
  const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                              VpiPoolKeeper(name_pool_), sim_ctx.GetArena()};

  for (const TimingCheckEntry& check : specify->GetTimingChecks()) {
    // §31.1 puts a timing check inside a specify block inside a module
    // declaration, so the check belongs to the instance that declared it, or
    // to the first top module where the prefix is empty.
    std::string_view scope =
        SpecifyEntryScope(check.inst_prefix, sim_ctx.FirstTopModule());
    if (scope.empty()) continue;
    // The walk makes any scope it has not met, so a prefix always has one.
    VpiHandle module = DesignObjectForFlatName(scope);

    auto* obj = AllocObject();
    obj->type = vpiTchk;
    obj->tchk_type = VpiTchkTypeOf(check.kind);
    obj->parent = module;
    module->children.push_back(
        obj);  // §37.3.4: the limits the check wrote, as vpiDelay reaches them.
    obj->delay_expr =
        VpiSourceDelayExpression(check.source_limits, check.inst_prefix,
                                 sim_ctx, [this] { return AllocObject(); });
    // §37.3.3: where the check was written.
    VpiRecordWrittenLocation(obj, check.loc, sim_ctx);

    // §37.40 (figure): "-> limit", retrieved with vpi_get_delays(), which
    // §38.10 has read as many delays as the check has limits.
    const int kLimits = LimitCountOf(check.kind);
    if (kLimits > 0) AddTchkLimit(obj, check.limit);
    if (kLimits > 1) AddTchkLimit(obj, check.limit2);

    obj->tchk_ref_term = MakeTchkTerm(
        AllocObject(), check.ref_signal,
        VpiTchkEventEdgeOf(check.ref_edge, check.ref_edge_descriptors), obj,
        name_pool_);
    // Detail 1: the data term denotes the data_event where the check has one; a
    // check written without one has no data signal and so no term.
    if (!check.data_signal.empty()) {
      obj->tchk_data_term = MakeTchkTerm(
          AllocObject(), check.data_signal,
          VpiTchkEventEdgeOf(check.data_edge, check.data_edge_descriptors), obj,
          name_pool_);
    }

    // §37.40 (figure): the notifier the check toggles, which is a register of
    // the same instance. A check written without one reaches none.
    if (!check.notifier.empty()) {
      obj->tchk_notifier = DesignObjectForFlatName(
          std::string(check.inst_prefix) + std::string(check.notifier));
    }

    // A check §32.9's $sdf_annotate registered was declared by no source, so
    // it has no arguments written to make.
    if (check.decl == nullptr) continue;
    FillTchkArguments(
        obj, *check.decl,
        ExpressionsIn(check.inst_prefix, object_map_, sim_ctx, kBuild),
        sim_ctx.GetArena());
  }
}

}  // namespace delta
