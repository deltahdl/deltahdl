#include <algorithm>
#include <cctype>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/vpi_user.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"

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
  // §37.5/§37.6/§37.9 (figure): the vpiDefaultDisableIff edge is drawn to an
  // enclosure with no name holding an expr and a distribution, and §37.4.1
  // makes such an enclosure a grouping of the objects in it. So what the edge
  // reaches is an expression or a distribution; a scope names at most one, so
  // it is the first child of either kind. Null where the scope wrote none.
  for (auto* child : scope->children) {
    if (VpiIsExprObject(child) || child->type == vpiDistribution) {
      return child;
    }
  }
  return nullptr;
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

std::vector<const UdpDecl*> VpiDesignUdpDecls(const RtlirDesign* design) {
  std::vector<const UdpDecl*> decls;
  if (design == nullptr) return decls;

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

void VpiFillUdpTableEntryObject(VpiObject* obj, const UdpTableRow& row,
                                VpiObject* defn) {
  obj->type = vpiTableEntry;
  // The symbol entries of a row are the input symbols it matches on, the
  // current state a sequential row carries, and the output symbol it names.
  obj->size = static_cast<int>(row.inputs.size()) +
              (row.current_state != 0 ? 1 : 0) + 1;
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
    module->children.push_back(obj);
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

// §37.40 (figure): the vpiEdge an event term reports - the edge control its
// timing_check_event was written with, and none where it was written without
// one.
static int VpiTchkTermEdgeOf(SpecifyEdge edge) {
  switch (edge) {
    case SpecifyEdge::kPosedge:
      return vpiPosedge;
    case SpecifyEdge::kNegedge:
      return vpiNegedge;
    default:
      return vpiNoEdge;
  }
}

// §37.40 (figure): one of the check's two event terms - the tchk term the
// vpiTchkRefTerm and vpiTchkDataTerm relations reach. Its own properties are
// the event's: the edge it was written with (vpiEdge) and the signal it names.
static VpiObject* MakeTchkTerm(VpiObject* term, std::string_view signal,
                               SpecifyEdge edge, VpiObject* tchk,
                               std::deque<std::string>& names) {
  term->type = vpiTchkTerm;
  names.emplace_back(signal);
  term->name = names.back();
  term->edge = VpiTchkTermEdgeOf(edge);
  term->parent = tchk;
  tchk->children.push_back(term);
  return term;
}

void VpiContext::AttachTimingChecks(SimContext& sim_ctx) {
  // §37.40 draws a tchk carrying the kind of check it is (vpiTchkType), the
  // limit vpi_get_delays() retrieves, the two event terms details 1 and 2 are
  // about, and the notifier it toggles. No pass built one, so the whole of the
  // subclause answered for no design: a module's vpiTchk iteration reached
  // none of the checks its specify block declared.
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;

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
    module->children.push_back(obj);

    // §37.40 (figure): "-> limit", retrieved with vpi_get_delays(). §31.2
    // writes a check's limit as the one time it is given, so the object
    // carries it as its single delay.
    VpiDelayInfo limit;
    limit.delay = static_cast<double>(check.limit);
    limit.min_delay = limit.delay;
    limit.typ_delay = limit.delay;
    limit.max_delay = limit.delay;
    obj->delays.push_back(limit);

    obj->tchk_ref_term = MakeTchkTerm(AllocObject(), check.ref_signal,
                                      check.ref_edge, obj, name_pool_);
    // Detail 1: the data term denotes the data_event where the check has one; a
    // check written without one has no data signal and so no term.
    if (!check.data_signal.empty()) {
      obj->tchk_data_term = MakeTchkTerm(AllocObject(), check.data_signal,
                                         check.data_edge, obj, name_pool_);
    }

    // §37.40 (figure): the notifier the check toggles, which is a register of
    // the same instance. A check written without one reaches none.
    if (!check.notifier.empty()) {
      obj->tchk_notifier = DesignObjectForFlatName(
          std::string(check.inst_prefix) + std::string(check.notifier));
    }
  }
}

}  // namespace delta
