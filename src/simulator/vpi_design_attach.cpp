#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <deque>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
// §37.44's vpiThread is defined in the SystemVerilog VPI header.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"

namespace delta {

namespace {

// The child of `parent` carrying this name, or null where it has none. §36.10
// makes each instance's objects "uniquely accessible", so one component of a
// flat name is matched against the children of the scope reached so far rather
// than against every object of the design.
VpiHandle ChildNamed(VpiHandle parent, std::string_view name) {
  for (auto* child : parent->children) {
    if (child->name == name) return child;
  }
  return nullptr;
}

// The object a flat design name already stands for, and null where the name
// reaches none. DesignObjectForFlatName below makes the scopes it passes
// through; this one makes nothing, which is what a reader that has something to
// say about an object the run built wants: a declaration the run built no
// object for is passed over rather than given an empty one.
VpiHandle FindObjectForFlatName(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    std::string_view flat_name) {
  std::vector<std::string_view> parts = VpiNamePathComponents(flat_name);
  if (parts.empty()) return nullptr;

  auto root = objects.find(parts.front());
  if (root == objects.end()) return nullptr;

  VpiHandle current = root->second;
  for (std::size_t i = 1; i < parts.size() && current != nullptr; ++i) {
    current = ChildNamed(current, parts[i]);
  }
  return current;
}

// §37.3.3: write the file and line of `loc` onto `obj`, which is what
// vpi_get(vpiLineNo) and vpi_get_str(vpiFile) then report for it. A declaration
// whose position the elaborator did not record says nothing about where the
// object stands, and a context attached to no run has no source description to
// resolve a file_id against; either leaves both properties as they were rather
// than reporting line zero and a file this tool invented.
void RecordSourceLocation(VpiHandle obj, SourceLoc loc,
                          const SourceManager* sources) {
  if (obj == nullptr || sources == nullptr || !loc.IsValid()) return;
  obj->line_no = static_cast<int>(loc.line);
  obj->file = std::string(sources->FilePath(loc.file_id));
}

// The source description a context attached to a run reads its locations
// against, and null for one attached to none.
const SourceManager* SourcesOf(SimContext* sim_ctx) {
  return sim_ctx == nullptr ? nullptr : &sim_ctx->GetDiag().Sources();
}

}  // namespace

VpiHandle VpiContext::DesignScopeChild(VpiHandle parent, std::string_view part,
                                       std::string_view full_path) {
  if (parent == nullptr) {
    auto it = object_map_.find(part);
    if (it != object_map_.end()) return it->second;
  } else {
    VpiHandle existing = ChildNamed(parent, part);
    if (existing != nullptr) return existing;
  }

  // The component names an instance the walk has not been through before, so
  // the scope it stands for is made here. A leaf is made the same way and then
  // told what it is by the caller, because what distinguishes the two is the
  // design object hanging off the name rather than anything in the name.
  name_pool_.emplace_back(part);
  auto* obj = AllocObject();
  obj->type = kVpiModule;
  obj->name = name_pool_.back();
  obj->full_name = std::string(full_path);
  obj->parent = parent;
  if (parent == nullptr) {
    object_map_[obj->name] = obj;
  } else {
    obj->index = static_cast<int>(parent->children.size());
    parent->children.push_back(obj);
  }
  return obj;
}

VpiHandle VpiContext::DesignObjectForFlatName(std::string_view flat_name) {
  std::vector<std::string_view> parts = VpiNamePathComponents(flat_name);
  if (parts.empty()) return nullptr;

  VpiHandle current = nullptr;
  std::size_t consumed = 0;
  for (std::string_view part : parts) {
    consumed += part.size();
    current = DesignScopeChild(current, part, flat_name.substr(0, consumed));
    consumed += 1;  // the separator this component was followed by
  }
  return current;
}

VpiHandle VpiContext::ThreadObjectFor(Process* proc) {
  if (proc == nullptr) return nullptr;
  auto it = thread_objects_.find(proc);
  if (it != thread_objects_.end()) {
    // §37.44 (vpiActive): the property belongs to the process, so it is read
    // when asked for rather than frozen into the object when it was made.
    it->second->active = proc->active;
    return it->second;
  }
  auto* obj = AllocObject();
  obj->type = vpiThread;
  obj->active = proc->active;
  thread_objects_[proc] = obj;
  return obj;
}

void VpiContext::RefreshThreadObjects() {
  if (sim_ctx_ == nullptr) return;
  for (Process* proc : sim_ctx_->GetScheduler().Threads()) {
    VpiHandle obj = ThreadObjectFor(proc);
    // §37.44 (thread one-to-many thread): the threads this one spawned, which
    // detail 1 calls "a branch of a fork construct". They hang off the parent
    // as its thread children, which is where VpiThreadThreads reads them and
    // where VpiThreadParent reads the link back.
    for (Process* child : proc->children) {
      VpiHandle child_obj = ThreadObjectFor(child);
      if (child_obj->parent != nullptr) continue;
      child_obj->parent = obj;
      obj->children.push_back(child_obj);
    }
  }
}

namespace {

// The first child of `obj` whose type is `type`, which is how this model links
// a frame to the frames and threads around it.
VpiObject* FirstChildOfType(VpiObject* obj, int type) {
  if (obj == nullptr) return nullptr;
  for (auto* child : obj->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiContext::ActivateFrame() {
  // §36.6: a run holding no PLI application has no design attached and nothing
  // to reach a frame through, so it pays nothing for this.
  if (sim_ctx_ == nullptr) return nullptr;

  VpiHandle outer = active_frame_;
  VpiHandle thread = ThreadObjectFor(sim_ctx_->CurrentProcess());
  // §37.43 detail 5: "The vpiParent relation shall indicate the frame from
  // which the child frame was activated." The outermost frame of a call chain
  // was activated from no frame, so it hangs off the thread instead, which is
  // the diagram's frame--thread edge and reports no parent frame.
  VpiHandle holder = outer != nullptr ? outer : thread;
  if (holder == nullptr) return nullptr;

  // A call chain of the same shape entered again reuses the frame already made
  // at this point in it. Detail 4 has at most one frame active at a time in a
  // thread, and what tells one activation from the next is which frame is
  // active rather than which object stands for it -- a design calling a
  // function a thousand times has one frame a thousand times over, not a
  // thousand objects.
  VpiObject* frame = FirstChildOfType(holder, vpiFrame);
  if (frame == nullptr) {
    frame = AllocObject();
    frame->type = vpiFrame;
    frame->parent = holder;
    holder->children.push_back(frame);
  }
  frame->active = true;
  active_frame_ = frame;
  return outer;
}

void VpiContext::RestoreActiveFrame(VpiHandle previous) {
  if (sim_ctx_ == nullptr) return;
  // §37.43 (vpiActive): the frame being left is no longer the active one, and
  // the frame it was activated from becomes active again.
  if (active_frame_ != nullptr) active_frame_->active = false;
  active_frame_ = previous;
  if (active_frame_ != nullptr) active_frame_->active = true;
}

VpiActiveFrameScope::VpiActiveFrameScope()
    : outer_(GetGlobalVpiContext().ActivateFrame()) {}

VpiActiveFrameScope::~VpiActiveFrameScope() {
  GetGlobalVpiContext().RestoreActiveFrame(outer_);
}

namespace {

// §37.14: the vpiDirection a declared port reports. A port declared with no
// direction, and §13's ref direction, which the diagram's port has no value
// for, report none.
int VpiPortDirectionOf(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return kVpiInput;
    case Direction::kOutput:
      return kVpiOutput;
    case Direction::kInout:
      return kVpiInout;
    default:
      return 0;
  }
}

// One port of a module instance, as the object §37.14's instance-to-port
// relation reaches. `index` is the position the module declared it in, which
// detail 9 has vpiPortIndex report and which starts at zero, and `size` is the
// width detail 6 has vpiScalar and vpiVector read -- "whether the port is 1 bit
// or more than 1 bit ... not anything about what is connected to the port".
void FillPortObject(VpiObject* obj, const RtlirPort& port, int index,
                    VpiHandle module, std::deque<std::string>& names) {
  obj->type = kVpiPort;
  names.emplace_back(port.name);
  obj->name = names.back();
  obj->index = index;
  obj->size = static_cast<int>(port.width);
  obj->direction = VpiPortDirectionOf(port.direction);
  obj->parent = module;
  module->children.push_back(obj);
}

// The instances `mod` holds, pushed onto the walk under their own paths. An
// instance's path is its parent's with its name on the end, which is the string
// the simulator keys every object of that instance under.
void PushChildInstances(
    const RtlirModule* mod, const std::string& prefix,
    std::vector<std::pair<const RtlirModule*, std::string>>& work) {
  work.reserve(work.size() + mod->children.size());
  for (const auto& child : mod->children) {
    std::string child_prefix = prefix;
    if (!child_prefix.empty()) child_prefix += '.';
    child_prefix += std::string(child.inst_name);
    work.emplace_back(child.resolved, child_prefix);
  }
}

// The flat name the simulator keys one declaration of this scope under: the
// instance path with the declared name on the end. A top module carries the
// empty prefix and keys its own declarations under their bare names.
std::string VpiFlatName(const std::string& prefix, std::string_view name) {
  if (prefix.empty()) return std::string(name);
  return prefix + "." + std::string(name);
}

// Every scope of the design, visited outward from each top module under the
// flat instance path the simulator keys that scope's objects under. A top
// carries the empty prefix, having no instantiation over it to be named by.
template <typename Visit>
void WalkInstancePaths(const RtlirDesign* design, Visit visit) {
  std::vector<std::pair<const RtlirModule*, std::string>> work;
  work.reserve(design->top_modules.size());
  for (auto* top : design->top_modules) work.emplace_back(top, std::string());

  while (!work.empty()) {
    auto [mod, prefix] = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    PushChildInstances(mod, prefix, work);
    visit(mod, prefix);
  }
}

// §37.3.3: "These properties are applicable to every object that corresponds to
// some object within the source code." Nothing under src/ ever wrote either
// one, so vpiLineNo answered zero and vpiFile answered NULL for every object of
// every design, and the two location properties could be read back only off an
// object a test had built and stamped by hand. Where an object stands is a fact
// about the declaration it was made from, which the run does not carry and the
// design does: this walks the design's declarations and tells each object the
// run built for one where it is.
// §36.12.1 Table 36-10 rows 3, 4 and 7: the object kind an elaborated variable
// carries. In the IEEE 1800 standards "these array types are always represented
// as vpiRegArray objects, and vpiIntegerVar and vpiTimeVar objects are always
// non-array variables", a real array is "exclusively represented as vpiRegArray
// objects", and a vpiRegArray iteration therefore "includes arrays of
// vpiIntegerVar, vpiTimeVar, and vpiRealVar". So an unpacked array is one kind
// whatever it holds, and every other variable is the kind it was declared.
int VpiVariableObjectKind(const RtlirVariable& var) {
  if (var.num_unpacked_dims > 0) return vpiRegArray;
  // A name declared through a typedef reports kNamed, so the flags the
  // elaborator resolved through the typedef answer first for the kinds that
  // have one.
  if (var.decl_kind == DataTypeKind::kShortreal) return vpiShortRealVar;
  if (var.is_real) return vpiRealVar;
  if (var.is_string) return vpiStringVar;
  if (var.is_chandle) return vpiChandleVar;
  switch (var.decl_kind) {
    case DataTypeKind::kInteger:
      return vpiIntegerVar;
    case DataTypeKind::kTime:
      return vpiTimeVar;
    case DataTypeKind::kByte:
      return vpiByteVar;
    case DataTypeKind::kShortint:
      return vpiShortIntVar;
    case DataTypeKind::kInt:
      return vpiIntVar;
    case DataTypeKind::kLongint:
      return vpiLongIntVar;
    case DataTypeKind::kBit:
      return vpiBitVar;
    case DataTypeKind::kEnum:
      return vpiEnumVar;
    case DataTypeKind::kStruct:
      return vpiStructVar;
    case DataTypeKind::kUnion:
      return vpiUnionVar;
    default:
      // §37.17 detail 19: a logic var and a reg are the same object kind, and
      // it is what a variable the clause draws no separate box for carries.
      return kVpiReg;
  }
}

// §36.12.1 Table 36-10: tell each object the run built for a variable which
// kind of variable it is. VpiContext::Attach stamps every one of them vpiReg,
// which rows 3, 4 and 7 rule out: a design's array variables were vpiRegArray
// objects to nothing, so a vpiRegArray iteration reached none of them, and an
// integer, time or real variable answered that it was a reg.
void RecordVariableObjectKinds(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : mod->variables) {
          VpiHandle obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj != nullptr) obj->type = VpiVariableObjectKind(var);
        }
      });
}

void RecordDeclarationSourceLocations(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager* sources) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : mod->nets) {
          RecordSourceLocation(
              FindObjectForFlatName(objects, VpiFlatName(prefix, net.name)),
              net.loc, sources);
        }
        for (const RtlirVariable& var : mod->variables) {
          RecordSourceLocation(
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name)),
              var.loc, sources);
        }
      });
}

}  // namespace

void VpiContext::AttachDesignPorts(const RtlirDesign* design) {
  // §37.14: the ports a module instance declares, as the objects the diagram's
  // one-to-many instance-to-port relation reaches. VpiContext::CreatePort could
  // make one and nothing under src/ called it, so a design's ports were not
  // objects at all and the whole of §37.14 answered only for ports a test built
  // itself.
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [this](const RtlirModule* mod, const std::string& prefix) {
        // A top module has no module object over it to hang ports from, the
        // same boundary the module paths meet.
        if (prefix.empty()) return;
        VpiHandle module = DesignObjectForFlatName(prefix);
        if (module == nullptr) return;

        module->children.reserve(module->children.size() + mod->ports.size());
        int index = 0;
        const SourceManager* sources = SourcesOf(sim_ctx_);
        for (const auto& port : mod->ports) {
          auto* obj = AllocObject();
          FillPortObject(obj, port, index++, module, name_pool_);
          // §37.3.3: a port is written in the source text, so its object stands
          // where the declaration does and reports it.
          RecordSourceLocation(obj, port.loc, sources);
        }
      });
}

namespace {

// §37.37: one end of an intermodule path as the connection that makes the path
// names it -- the instance whose port it is, the port's own name, the signal of
// the enclosing scope the instantiation connected it to, and the direction that
// says which end of a path the port can be.
struct InterModPortRef {
  std::string inst_path;
  std::string_view port_name;
  std::string_view signal;
  Direction direction;
};

// §37.37: one intermodule path, as the two ports it runs between.
struct InterModConnection {
  std::string from_inst;
  std::string_view from_port;
  std::string to_inst;
  std::string_view to_port;
};

// The signal of the enclosing scope a port connection names. §23.3.2 lets the
// actual be an expression, and an expression names no single signal two ports
// can both be on, so only a connection written as a plain name puts its port
// where a path can reach it.
std::string_view ConnectedSignalName(const Expr* conn) {
  if (conn == nullptr || conn->kind != ExprKind::kIdentifier) return {};
  return conn->text;
}

// §37.37: an intermodule path runs from the port driving a signal to a port
// receiving it, which makes an inout port either end and a port that is neither
// no end at all. The two ends are distinct ports of one signal.
bool InterModPathRuns(const InterModPortRef& from, const InterModPortRef& to) {
  if (&from == &to) return false;
  if (from.signal != to.signal) return false;
  const bool kDrives = from.direction == Direction::kOutput ||
                       from.direction == Direction::kInout;
  const bool kReceives =
      to.direction == Direction::kInput || to.direction == Direction::kInout;
  return kDrives && kReceives;
}

// Every port the instances of `mod` connect to a signal of `mod`'s own scope.
// A path within this scope runs between two of them.
void CollectScopePortRefs(const RtlirModule* mod, const std::string& prefix,
                          std::vector<InterModPortRef>& refs) {
  for (const auto& child : mod->children) {
    std::string inst_path = prefix;
    if (!inst_path.empty()) inst_path += '.';
    inst_path += std::string(child.inst_name);
    refs.reserve(refs.size() + child.port_bindings.size());
    for (const auto& binding : child.port_bindings) {
      std::string_view signal = ConnectedSignalName(binding.connection);
      if (signal.empty()) continue;
      refs.push_back({inst_path, binding.port_name, signal, binding.direction});
    }
  }
}

// The paths running out of one port: one to each port of the same signal that
// receives what this one drives.
void PairOnePortRef(const InterModPortRef& from,
                    const std::vector<InterModPortRef>& refs,
                    std::vector<InterModConnection>& out) {
  out.reserve(out.size() + refs.size());
  for (const auto& to : refs) {
    if (!InterModPathRuns(from, to)) continue;
    out.push_back({from.inst_path, from.port_name, to.inst_path, to.port_name});
  }
}

// The paths one scope's connections make: every ordered pair of that scope's
// connected ports a signal runs between.
void PairScopePortRefs(const std::vector<InterModPortRef>& refs,
                       std::vector<InterModConnection>& out) {
  for (const auto& from : refs) PairOnePortRef(from, refs, out);
}

// Every intermodule path the design makes, gathered by walking the instance
// paths outward from each top the way the ports themselves are.
void CollectInterModConnections(const RtlirDesign* design,
                                std::vector<InterModConnection>& out) {
  WalkInstancePaths(design,
                    [&out](const RtlirModule* mod, const std::string& prefix) {
                      // A path is a connection between two of one scope's
                      // instances, so the scope holding the instantiations is
                      // where both its ends are named.
                      std::vector<InterModPortRef> refs;
                      CollectScopePortRefs(mod, prefix, refs);
                      PairScopePortRefs(refs, out);
                    });
}

// The port object one end of a path names, which AttachDesignPorts made. A
// connection naming a port its module does not declare has none to name.
VpiObject* DesignPortObject(VpiHandle module, std::string_view port_name) {
  if (module == nullptr) return nullptr;
  for (auto* child : module->children) {
    if (child->type == kVpiPort && child->name == port_name) return child;
  }
  return nullptr;
}

}  // namespace

void VpiContext::AttachDesignInterModPaths(const RtlirDesign* design) {
  // §37.37: an intermodule path runs between the ports of two module instances,
  // and detail 1 says how a PLI application gets to one -- "vpi_handle_multi(
  // vpiInterModPath, port1, port2) can be used". Nothing under src/ made one,
  // so a run held no intermodule path at all and the whole of this model
  // answered for paths a test had built and for none a design connected.
  if (design == nullptr) return;

  std::vector<InterModConnection> conns;
  CollectInterModConnections(design, conns);
  for (const InterModConnection& conn : conns) {
    VpiObject* from = DesignPortObject(DesignObjectForFlatName(conn.from_inst),
                                       conn.from_port);
    VpiObject* to =
        DesignPortObject(DesignObjectForFlatName(conn.to_inst), conn.to_port);
    if (from == nullptr || to == nullptr) continue;

    auto* path = AllocObject();
    path->type = vpiInterModPath;
    // §37.37 (the diagram's one-to-many relation to ports): the ports the path
    // runs between, and the link back from each of them, which is where
    // vpi_handle_multi() finds the path the two ports are both on.
    path->children.push_back(from);
    path->children.push_back(to);
    from->children.push_back(path);
    to->children.push_back(path);
  }
}

void VpiContext::AttachModuleDefNames(SimContext& sim_ctx) {
  // §38.11's example is what a definition name is for: vpi_handle_by_name
  // reaches an instance and vpi_get_str(vpiDefName, mod) says what it is an
  // instance of -- "Module top.mod1 is an instance of %s". The instance's own
  // name is vpiName and is the answer to a different question, so a module
  // reporting it here said that top.mod1 is an instance of mod1.
  //
  // The run has the answer already: the lowerer records each instance's module
  // type against the instance path, which is the same string the module object
  // carries as its vpiFullName.
  for (auto* obj : all_objects_) {
    if (obj->type != kVpiModule || obj->full_name.empty()) continue;
    std::string_view type = sim_ctx.FindInstanceType(obj->full_name);
    if (!type.empty()) obj->def_name = std::string(type);
  }
}

void VpiContext::AttachModulePathDelays(SimContext& sim_ctx) {
  // §38.10: "the VPI routine vpi_get_delays() shall retrieve the delays or
  // pulse limits of an object". A module path is one of the four kinds of
  // object the clause gives legal no_of_delays values for, and it is the one
  // whose twelve transition delays the clause takes without interpreting them
  // -- the 12-value row of Table 38-2 is the path's own array. No object a run
  // built carried a delay at all, so the routine had only what a caller put in
  // an object of its own making to retrieve.
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;

  for (const PathDelay& path : specify->GetPathDelays()) {
    // §30.3 puts a specify block inside a module declaration, so the paths it
    // declares belong to the instance that declared them. A path of a module
    // elaborated as a top carries the empty prefix and has no module object
    // over it to hang from.
    if (path.inst_prefix.empty()) continue;
    std::string_view scope = path.inst_prefix;
    scope.remove_suffix(1);  // the prefix ends in the separator
    VpiHandle module = DesignObjectForFlatName(scope);
    if (module == nullptr) continue;

    auto* obj = AllocObject();
    obj->type = vpiModPath;
    obj->parent = module;
    module->children.push_back(obj);
    // §38.10: "the application-allocated s_vpi_delay array shall contain delays
    // in the same order in which they occur in the SystemVerilog description",
    // which for a module path is the order of its transition slots, and the
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

VpiObject* VpiContext::NetSourceDelayExpression(SimContext& sim_ctx,
                                                const RtlirNet& net) {
  // §37.3.4: the vpiDelay expression "shall be either an expression that
  // evaluates to a constant if there is only one delay specified or an
  // operation if there are more than one delay specified. If multiple delays
  // are specified, then the operation's vpiOpType shall be vpiListOp."
  //
  // §28.16's rise, fall and turn-off delays survive elaboration on RtlirNet in
  // the order the declaration wrote them, and the slots fill left to right, so
  // the first empty one ends the list the source specified.
  Expr* const written[3] = {net.delay_rise, net.delay_fall, net.delay_turnoff};
  std::vector<VpiObject*> constants;
  for (Expr* delay : written) {
    if (delay == nullptr) break;
    // Each written delay stands as a constant expression carrying the value
    // evaluating it produced. The storage goes on the run's arena rather than
    // through SimContext::CreateVariable, which would enter the delay under a
    // name the design never declared.
    auto* constant = AllocObject();
    constant->type = vpiConstant;
    constant->const_type = vpiIntConst;
    auto* storage = sim_ctx.GetArena().Create<Variable>();
    storage->value = EvalExpr(delay, sim_ctx, sim_ctx.GetArena());
    constant->var = storage;
    constant->size = static_cast<int>(storage->value.width);
    constants.push_back(constant);
  }

  if (constants.empty()) return nullptr;
  if (constants.size() == 1) return constants.front();

  // The operands of an operation are its expression children (§36.10.3), so the
  // delays hang there in the order the declaration wrote them.
  auto* op = AllocObject();
  op->type = vpiOperation;
  op->op_type = vpiListOp;
  for (VpiObject* constant : constants) op->children.push_back(constant);
  return op;
}

void VpiContext::AttachSourceDelayExpressions(SimContext& sim_ctx,
                                              const RtlirDesign* design) {
  // §37.3.4: "To access the delay expressions that are specified within the
  // SystemVerilog source code, use the method vpiDelay."
  //
  // VpiObject::delay_expr is where vpi_handle(vpiDelay, obj) reads that
  // expression from, and nothing under src/ wrote it, so the relation answered
  // NULL for every object of every design and a delay the source did write was
  // reachable only through vpi_get_delays() - which §37.3.4 gives to the other
  // question, the actual delays the tool is using.
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : mod->nets) {
          VpiHandle obj =
              FindObjectForFlatName(object_map_, VpiFlatName(prefix, net.name));
          if (obj == nullptr) continue;
          obj->delay_expr = NetSourceDelayExpression(sim_ctx, net);
        }
      });
}

void VpiContext::Attach(SimContext& sim_ctx, const RtlirDesign* design) {
  // §37.44: the run the thread objects are made against. They cannot all be
  // made here -- a fork branch begins while the design executes, long after
  // this -- so what is kept is the run itself.
  sim_ctx_ = &sim_ctx;

  // §36.10: "VPI routines provide access to objects in an instantiated
  // SystemVerilog design. An instantiated design is one where each instance of
  // an object is uniquely accessible. For instance, if a module m contains wire
  // w and is instantiated twice as m1 and m2, then m1.w and m2.w are two
  // distinct objects, each with its own set of related objects and properties."
  //
  // The simulator has that already: it keys each instance's object on a flat
  // string carrying the instance prefix, so m1.w and m2.w are two entries over
  // two Nets. What was missing was the shape §38.21 walks -- the name was
  // entered whole and resolved a component at a time, so nothing but a
  // top-level name ever matched -- and the nets, which were not entered at all
  // though a wire is the clause's own example of an object VPI reaches.
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || var == nullptr) continue;
    obj->type = kVpiReg;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
  }
  AttachModuleDefNames(sim_ctx);
  AttachModulePathDelays(sim_ctx);
  for (auto& [name, net] : sim_ctx.GetNets()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || net == nullptr) continue;
    obj->type = kVpiNet;
    obj->net = net;
    // The same pairing CreateNetObj makes: a net answers a value query out of
    // the storage its resolution writes, so the object carries that storage
    // beside the net itself.
    if (net->resolved != nullptr) {
      obj->var = net->resolved;
      obj->size = static_cast<int>(net->resolved->value.width);
    }
  }
  AttachSourceDelayExpressions(sim_ctx, design);
  RecordVariableObjectKinds(design, object_map_);
  RecordDeclarationSourceLocations(design, object_map_, SourcesOf(sim_ctx_));
  AttachTopModules(design);
}

void VpiContext::AttachTopModules(const RtlirDesign* design) {
  // §37.5 detail 1: "Top-level modules shall be accessed using vpi_iterate()
  // with a NULL reference object", which is where a PLI application walking a
  // design begins. Nothing built an object for a top module: the simulator keys
  // an instance's objects on a flat name and a top carries the empty prefix, so
  // what the passes above entered were the top's own contents under their bare
  // names and the top itself was an object of no kind. The iteration that
  // reaches the tops therefore reached none of them, VpiObject::top_module was
  // read by that filter and by vpi_get(vpiTopModule) and was written by
  // nothing, and §37.1's "using VPI data models" had no first step.
  if (design == nullptr) return;

  for (auto* top : design->top_modules) {
    if (top == nullptr) continue;
    // The objects already entered under bare names are the top's contents, so
    // they become its children and it becomes their enclosing instance. They
    // stay keyed under those names, which is what the simulator keys their
    // storage on and what vpi_handle_by_name() has always answered to.
    std::vector<VpiObject*> contents;
    for (auto& [name, object] : object_map_) {
      if (object != nullptr && object->parent == nullptr) {
        contents.push_back(object);
      }
    }

    name_pool_.emplace_back(top->name);
    auto* obj = AllocObject();
    obj->type = kVpiModule;
    obj->name = name_pool_.back();
    obj->full_name = std::string(top->name);
    obj->top_module = true;
    for (auto* object : contents) {
      object->parent = obj;
      obj->children.push_back(object);
    }
    object_map_[obj->name] = obj;
  }
}

void AttachDesignToPliApplications(const RtlirDesign* design, SimContext& ctx) {
  VpiContext& vpi = GetGlobalVpiContext();
  // §36.9's two registrations are what a PLI application has become part of
  // this tool by, so between them they say whether the run holds one at all.
  // A run holding neither has nobody to call the library, and the design it
  // would answer with is left unbuilt rather than built for no reader.
  if (vpi.RegisteredSystfs().empty() && vpi.RegisteredCallbacks().empty()) {
    return;
  }
  vpi.Attach(ctx, design);
  vpi.AttachDesignPorts(design);
  // §37.37: the paths run between the port objects the line above made, so they
  // are gathered once those exist.
  vpi.AttachDesignInterModPaths(design);
}

}  // namespace delta
