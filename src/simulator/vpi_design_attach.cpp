#include "simulator/vpi_design_attach.h"

#include <cstddef>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_io_decl.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_typespecs.h"
#include "simulator/vpi_design_viewports.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_source_delay.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.3.3: write the file and line of `loc` onto `obj`, which is what
// vpi_get(vpiLineNo) and vpi_get_str(vpiFile) then report for it. A declaration
// whose position the elaborator did not record says nothing about where the
// object stands, and a context attached to no run has no source description to
// resolve a file_id against; either leaves both properties as they were rather
// than reporting line zero and a file this tool invented.
void RecordSourceLocation(VpiHandle obj, SourceLoc loc,
                          const SourceManager* sources) {
  if (obj == nullptr || sources == nullptr || !loc.IsValid()) return;
  // A declaration read through the preprocessor stands in the text it joined
  // from the sources, and its position is reported where it was written: the
  // file and line that line of the joined text came from.
  const SourceLoc kWritten = sources->ResolveToOrigin(loc);
  obj->line_no = static_cast<int>(kWritten.line);
  obj->file = std::string(sources->FilePath(kWritten.file_id));
}

// §37.3.6: mark `obj` protected where `loc` stands in code a decryption
// envelope contained. A context attached to no run has no source description
// to ask and marks nothing.
void RecordProtection(VpiHandle obj, SourceLoc loc,
                      const SourceManager* sources) {
  if (obj == nullptr || sources == nullptr) return;
  if (sources->IsProtected(loc)) obj->is_protected = true;
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
  std::vector<std::string_view> parts =
      VpiNamePathComponents(flat_name, dotted_escaped_names_);
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

namespace {

// §37.14: the vpiDirection a declared port reports, vpiRef for one passed by
// reference as §37.13 detail 1 has its io decl report. A port declared with no
// direction reports none.
int VpiPortDirectionOf(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return kVpiInput;
    case Direction::kOutput:
      return kVpiOutput;
    case Direction::kInout:
      return kVpiInout;
    case Direction::kRef:
      return vpiRef;
    default:
      return 0;
  }
}

// One port of a module instance, as the object §37.14's instance-to-port
// relation reaches. `index` is the position the module declared it in, which
// detail 9 has vpiPortIndex report and which starts at zero, and `size` is the
// width detail 6 has vpiScalar and vpiVector read -- whether the port itself is
// one bit wide or wider, whatever is connected to it. Detail 1 has its type
// follow the formal, a modport port's naming a modport of its interface, and
// detail 8 has it say whether it was written with a name of its own.
void FillPortObject(VpiObject* obj, const RtlirPort& port, int index,
                    VpiHandle module, std::deque<std::string>& names) {
  obj->type = kVpiPort;
  names.emplace_back(port.name);
  obj->name = names.back();
  obj->index = index;
  obj->size = static_cast<int>(port.width);
  obj->direction = VpiPortDirectionOf(port.direction);
  obj->port_type = VpiPortTypeFromFormal(
      port.is_interface_port, !port.declared_type->modport_name.empty());
  obj->explicit_name = port.is_explicit_named;
  obj->parent = module;
  module->children.push_back(obj);
}

// §37.13 with §37.5: the io decl `decl` is, under `module`. Its vpiExpr is
// `item`, the net or variable the declaration makes or names (detail 2),
// through a ref obj for a ref port or an interface port, the second of which
// has no direction (details 1 and 3).
void MakeModuleIoDecl(const RtlirIoDecl& decl, VpiHandle module,
                      VpiObject* item, const std::function<VpiObject*()>& alloc,
                      std::deque<std::string>& names) {
  VpiObject* io_decl = alloc();
  io_decl->type = vpiIODecl;
  names.emplace_back(decl.name);
  io_decl->name = names.back();
  io_decl->full_name = VpiScopedFullName(module, decl.name);
  io_decl->parent = module;
  const bool kByRef = decl.direction == Direction::kRef;
  io_decl->direction = VpiIoDeclDirection(
      VpiPortDirectionOf(decl.direction), kByRef, decl.is_interface_port,
      /*expr_is_virtual_interface_var=*/false);
  io_decl->io_expr = item;
  if (kByRef || decl.is_interface_port) {
    VpiObject* ref_obj = alloc();
    ref_obj->type = vpiRefObj;
    ref_obj->parent = io_decl;
    ref_obj->name = io_decl->name;
    ref_obj->full_name = io_decl->full_name;
    ref_obj->actual = item;
    io_decl->io_expr = ref_obj;
  }
  module->children.push_back(io_decl);
}

// The net or variable the io decl of the port `port` reaches through vpiExpr,
// under the instance `prefix` names; none for an interface port, whose ref obj
// is bound once its connection is known (§37.15).
VpiObject* PortIoDeclItem(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const std::string& prefix, const RtlirPort& port) {
  if (port.is_interface_port) return nullptr;
  return FindObjectForFlatName(objects, VpiFlatName(prefix, port.name));
}

// The net or variable the io decl of `decl` reaches through vpiExpr, under the
// instance `prefix` names; null where the declaration's expression is no single
// name (§37.13).
VpiObject* IoDeclItem(
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const std::string& prefix, const RtlirIoDecl& decl) {
  if (decl.object_name.empty()) return nullptr;
  return FindObjectForFlatName(objects, VpiFlatName(prefix, decl.object_name));
}

// §37.24 (figure): the interconnect net a port declared with the `interconnect`
// keyword stands for. §37.24's whole model is about these objects and no pass
// made one, so a design declaring a generic interconnect port had no
// interconnect net at all: the vpiElement and vpiMember rules of detail 1 and
// the dimension-at-a-time walk of detail 2 ran only over objects a test built.
//
// The net is hung in the instance the port belongs to and is the port's
// §37.14 vpiLowConn - the connection inside the instance - which is what an
// application walking in from the port reaches. A port declaring an unpacked
// dimension stands for an interconnect array instead (§37.24 details 1 and 2).
void FillInterconnectNetObject(VpiObject* obj, const RtlirPort& port,
                               VpiObject* port_obj,
                               std::deque<std::string>& names,
                               const std::function<VpiObject*()>& alloc) {
  VpiHandle module = port_obj->parent;
  obj->type = vpiInterconnectNet;
  names.emplace_back(port.name);
  obj->name = names.back();
  obj->size = static_cast<int>(port.width);
  obj->parent = module;
  module->children.push_back(obj);
  port_obj->low_conn = obj;
  VpiMakeInterconnectArray(obj, port, alloc, names);
}

// §37.3.3: the location properties apply to every object that stands for
// something in the source code. Nothing under src/ ever wrote either
// one, so vpiLineNo answered zero and vpiFile answered NULL for every object of
// every design, and the two location properties could be read back only off an
// object a test had built and stamped by hand. Where an object stands is a fact
// about the declaration it was made from, which the run does not carry and the
// design does: this walks the design's declarations and tells each object the
// run built for one where it is.
// §36.12.1 Table 36-10 rows 3, 4 and 7: the object kind an elaborated variable
// carries. In the IEEE 1800 standards those arrays are always vpiRegArray
// objects while vpiIntegerVar and vpiTimeVar objects are never arrays, a real
// array is a vpiRegArray object and nothing else, and so a vpiRegArray
// iteration takes in arrays of integer, time and real variables. So an unpacked
// array is one kind whatever it holds, and every other variable is the kind it
// was declared.
int VpiVariableObjectKind(const RtlirVariable& var) {
  // §37.62 (figure): the object an event statement triggers is a named event,
  // and §37.27 draws the array of them beside it. A named event is not a
  // variable holding a value, so Table 36-10's rule that an unpacked array of
  // variables is one vpiRegArray object says nothing about it and the event
  // kinds answer ahead of that rule. Without this an event declaration's object
  // was a reg, so the arrow §37.62 draws from an event statement reached an
  // object of a kind the figure has no box for.
  if (var.is_event) {
    return var.num_unpacked_dims > 0 ? vpiNamedEventArray : vpiNamedEvent;
  }
  // §37.17 detail 1 with Table 36-10: an array of variables is one array var,
  // whether its unpacked dimension is fixed or a queue's, a dynamic array's or
  // an associative array's.
  if (var.num_unpacked_dims > 0 || var.is_queue || var.is_dynamic ||
      var.is_assoc) {
    return vpiRegArray;
  }
  // A name declared through a typedef reports kNamed, so the flags the
  // elaborator resolved through the typedef answer first for the kinds that
  // have one.
  // §37.33: a variable declared with a class type is the clause's "class var",
  // the object every rule of the subclause is written about. A class type is
  // named rather than a DataTypeKind of its own, so decl_kind leaves it in the
  // kNamed default and the variable was stamped vpiReg: a design's class
  // variables were class vars to nothing, vpiObjId and vpiClassObj answered for
  // none of them, and a vpiClassVar iteration reached none.
  if (!var.class_type_name.empty()) return vpiClassVar;
  if (var.decl_kind == DataTypeKind::kShortreal) return vpiShortRealVar;
  if (var.is_real) return vpiRealVar;
  if (var.is_string) return vpiStringVar;
  if (var.is_chandle) return vpiChandleVar;
  // A variable declared with an enum typedef reports kNamed; the enum it names
  // makes it an enum var all the same.
  if (!var.enum_type_name.empty()) return vpiEnumVar;
  // §37.17 detail 19: a logic var and a reg are the same object kind, and it
  // is what a variable the clause draws no separate box for carries.
  return VpiDataTypeVariableKind(var.decl_kind);
}

// §25.9: the interface the virtual interface variable `var` refers to an
// instance of, as the design declares it; null for any other variable.
const RtlirModule* VifInterfaceOf(const RtlirDesign& design,
                                  const RtlirVariable& var) {
  if (var.written_type == nullptr ||
      var.written_type->kind != DataTypeKind::kVirtualInterface) {
    return nullptr;
  }
  const auto kFound = design.all_modules.find(var.written_type->type_name);
  return kFound != design.all_modules.end() ? kFound->second : nullptr;
}

// §36.12.1 Table 36-10: tell each object the run built for a variable which
// kind of variable it is. VpiContext::Attach stamps every one of them vpiReg,
// which rows 3, 4 and 7 rule out: a design's array variables were vpiRegArray
// objects to nothing, so a vpiRegArray iteration reached none of them, and an
// integer, time or real variable answered that it was a reg. The variable an
// ANSI variable port declares is told as the body's are (VpiDeclaredVariables).
void RecordVariableObjectKinds(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          VpiHandle obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr) continue;
          obj->type = VpiVariableObjectKind(var);
          // §37.17 (printed page 1025) with §6.20.6: a variable declared
          // const is a constant variable.
          obj->decl_facts.constant_variable =
              var.written_type != nullptr && var.written_type->is_const;
          obj->decl_facts.vif_interface = VifInterfaceOf(*design, var);
          // §37.29: a virtual interface var of a modport's type is a modport.
          obj->is_modport = var.written_type != nullptr &&
                            !var.written_type->modport_name.empty();
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

// §37.3.6: the objects that represent code a decryption envelope contained --
// the instance of a module declared in one, and a net or variable declared in
// one -- report vpiIsProtected TRUE, and the access §37.3.6 makes an error is
// refused for them. Run once the tops have adopted their contents, so a top
// module is found under its own name like any other instance.
void RecordProtectedDeclarations(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects,
    const SourceManager* sources) {
  if (design == nullptr) return;

  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        std::string_view instance = prefix.empty() ? mod->name : prefix;
        RecordProtection(FindObjectForFlatName(objects, instance), mod->loc,
                         sources);
        for (const RtlirNet& net : mod->nets) {
          RecordProtection(
              FindObjectForFlatName(objects, VpiFlatName(prefix, net.name)),
              net.loc, sources);
        }
        for (const RtlirVariable& var : mod->variables) {
          RecordProtection(
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

  const std::function<VpiObject*()> kAlloc = [this] { return AllocObject(); };
  const VpiNameKeeper kKeep = VpiPoolKeeper(name_pool_);
  // §37.5: a top module reaches its ports as any instance does, keyed under
  // its own name since AttachTopModules made its object.
  WalkInstanceObjects(
      design, object_map_,
      [this, &kAlloc](const RtlirModule* mod, const std::string& prefix,
                      VpiHandle module) {
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
          RecordProtection(obj, port.loc, sources);
          if (port.is_interconnect) {
            FillInterconnectNetObject(AllocObject(), port, obj, name_pool_,
                                      kAlloc);
          }
          // A port written as an expression stands for no declaration of its
          // own; port_expr_decls holds those it names.
          if (port.port_expr == nullptr) {
            MakeModuleIoDecl(
                {port.name, port.direction, port.name, port.is_interface_port},
                module, PortIoDeclItem(object_map_, prefix, port), kAlloc,
                name_pool_);
          }
        }
        for (const RtlirIoDecl& decl : mod->port_expr_decls) {
          MakeModuleIoDecl(decl, module, IoDeclItem(object_map_, prefix, decl),
                           kAlloc, name_pool_);
        }
      });
  if (sim_ctx_ == nullptr) return;
  // §37.42: a connection's calls are shaped once every connection is made.
  std::vector<VpiDeferredCall> deferred;
  const VpiAttachBuild kBuild{kAlloc, kKeep, sim_ctx_->GetArena(), &deferred};
  AttachPortConnections(design, object_map_, *sim_ctx_, kBuild);
  VpiShapeDeferredCalls(design, object_map_, deferred, CallBuild(), kBuild);
  // §37.83: the attributes each port is written with.
  AttachPortAttributes(design, object_map_, *sim_ctx_, kBuild);
  AttachPortTypespecs(design, object_map_, call_objects_, *sim_ctx_, kBuild);
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
  // and detail 1 has a PLI application reach one with
  // vpi_handle_multi(vpiInterModPath, port1, port2). Nothing under src/ made
  // one, so a run held no intermodule path at all and the whole of this model
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

void VpiContext::AttachSourceDelayExpressions(SimContext& sim_ctx,
                                              const RtlirDesign* design) {
  // §37.3.4: the delay expressions the source code writes are reached through
  // vpiDelay.
  //
  // VpiObject::delay_expr is where vpi_handle(vpiDelay, obj) reads that
  // expression from, and nothing under src/ wrote it, so the relation answered
  // NULL for every object of every design and a delay the source did write was
  // reachable only through vpi_get_delays() - which §37.3.4 gives to the other
  // question, the actual delays the tool is using.
  if (design == nullptr) return;

  WalkInstancePaths(design, [&](const RtlirModule* mod,
                                const std::string& prefix) {
    for (const RtlirNet& net : mod->nets) {
      VpiHandle obj =
          FindObjectForFlatName(object_map_, VpiFlatName(prefix, net.name));
      if (obj == nullptr) continue;
      // §28.16's rise, fall and turn-off delays survive elaboration on
      // RtlirNet in the order the declaration wrote them, and the slots
      // fill left to right, so the first empty one ends the list.
      obj->delay_expr = VpiSourceDelayExpression(
          {net.delay_rise, net.delay_fall, net.delay_turnoff},
          VpiFlatName(prefix, ""), sim_ctx, [this] { return AllocObject(); });
    }
  });
}

// §37.36 (figure): the UDP definitions of the design. A udp defn is drawn from
// a circle, so it belongs to no scope and is reached with a NULL reference
// object; nothing built one, so every property and relation the figure draws on
// it answered for no design at all.
void VpiContext::AttachUdpDefns(const RtlirDesign* design) {
  for (const UdpDecl* decl : VpiDesignUdpDecls(design)) {
    auto* defn = AllocObject();
    VpiFillUdpDefnObject(defn, *decl, name_pool_);
    // §37.3.6: a primitive declared in a decryption envelope is protected.
    RecordProtection(defn, decl->range.start, SourcesOf(sim_ctx_));
    run_objects_.try_emplace(decl, defn);
    // §37.13 with §29.3: an io decl per port the primitive declares, its one
    // output first and then its inputs, each one bit and declaring no net of
    // the defn's own.
    const auto kIoDecl = [&](std::string_view name, int direction) {
      auto* io_decl = AllocObject();
      io_decl->type = vpiIODecl;
      name_pool_.emplace_back(name);
      io_decl->name = name_pool_.back();
      io_decl->full_name = std::string(decl->name) + "." + std::string(name);
      io_decl->parent = defn;
      io_decl->direction = direction;
      io_decl->size = 1;
      defn->children.push_back(io_decl);
    };
    kIoDecl(decl->output_name, vpiOutput);
    for (std::string_view input : decl->input_names) kIoDecl(input, vpiInput);
    for (const UdpTableRow& row : decl->table) {
      VpiFillUdpTableEntryObject(AllocObject(), row, defn,
                                 sim_ctx_->GetArena());
    }
    // §37.36 (figure): the initial statement of a sequential UDP, which gives
    // the output its run begins with (§29.3.3).
    if (decl->has_initial) {
      auto* initial = AllocObject();
      initial->type = vpiInitial;
      initial->parent = defn;
      initial->body = VpiUdpInitialStatement(
          *decl, initial, [this] { return AllocObject(); }, name_pool_,
          sim_ctx_->GetArena());
      defn->children.push_back(initial);
    }
  }
}

void VpiContext::Attach(SimContext& sim_ctx, const RtlirDesign* design) {
  // §37.44: the run the thread objects are made against. They cannot all be
  // made here -- a fork branch begins while the design executes, long after
  // this -- so what is kept is the run itself.
  sim_ctx_ = &sim_ctx;
  dotted_escaped_names_ = VpiDottedEscapedNames(design);

  // §36.10: VPI routines reach the objects of an instantiated design, one in
  // which every instance of an object can be reached on its own. The clause's
  // example is a module m declaring wire w and instantiated as m1 and m2, where
  // m1.w and m2.w are separate objects, each with its own related objects and
  // properties.
  //
  // The simulator has that already: it keys each instance's object on a flat
  // string carrying the instance prefix, so m1.w and m2.w are two entries over
  // two Nets. What was missing was the shape §38.21 walks -- the name was
  // entered whole and resolved a component at a time, so nothing but a
  // top-level name ever matched -- and the nets, which were not entered at all
  // though a wire is the clause's own example of an object VPI reaches.
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    // §37.10 detail 6: an imported item is not reached through the scope that
    // imported it, the key the import enters being the run's; and by §37.12 a
    // named block's variable hangs from the block, which the block walk makes.
    if (sim_ctx.IsImportedName(name) || sim_ctx.IsBlockVariable(name)) continue;
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || var == nullptr) continue;
    obj->type = kVpiReg;
    // §37.61 detail 3: a variable the run declares statically has an actual.
    obj->actual_origin = kVpiActualStaticElab;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
  }
  AttachInstanceObjects(design);
  AttachModuleDefNames(sim_ctx);
  for (auto& [name, net] : sim_ctx.GetNets()) {
    VpiHandle obj = DesignObjectForFlatName(name);
    if (obj == nullptr || net == nullptr) continue;
    obj->type = kVpiNet;
    obj->actual_origin = kVpiActualStaticElab;
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
  AttachPackages(design);
  AttachTopModules(design);
  // §37.39 and §37.40: the paths and checks a specify block declares, made from
  // the run's SpecifyManager once the tops have objects, since the first top's
  // own hang from it.
  AttachModulePathDelays(sim_ctx);
  AttachTimingChecks(sim_ctx);
  // §37.35: the UDP definitions are made ahead of the instances' contents,
  // whose udps reach them.
  AttachUdpDefns(design);
  AttachInstanceContents(design);
  RecordProtectedDeclarations(design, object_map_, SourcesOf(sim_ctx_));
  RecordViewportGrants(design, object_map_, sim_ctx.GetDiag().Sources());
  // §37.23: the scope a nettype declaration hangs in is the one the top has
  // just adopted, so the declarations are made once those scopes are final.
  AttachNettypeDeclarations(design);
}

namespace {

// §37.4.2 reads a diagram's `str: vpiFullName` with vpi_get_str, and §37.3.1
// writes what that string is: the hierarchical path name a design is reached by
// -- "top.m1.w" for the wire w of the instance m1 of the top module top. An
// object entered under a flat name that began below the top carries only the
// part of that path below it, so the top's own name is put back on the front of
// every full name in the subtree it has just adopted.
void PrefixFullNamesWithTop(VpiObject* obj, std::string_view top) {
  if (obj == nullptr) return;
  if (!obj->full_name.empty()) {
    obj->full_name = std::string(top) + "." + obj->full_name;
  }
  for (auto* child : obj->children) PrefixFullNamesWithTop(child, top);
}

}  // namespace

void VpiContext::MakeNettypeDecls(VpiHandle scope,
                                  const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* entry : items) {
    if (entry->kind != ModuleItemKind::kNettypeDecl) continue;
    const ModuleItem& item = *entry;
    name_pool_.emplace_back(item.name);
    auto* decl = AllocObject();
    decl->type = vpiNettypeDecl;
    decl->name = name_pool_.back();
    decl->full_name = VpiScopedFullName(scope, item.name);
    decl->parent = scope;
    // §37.10 detail 6: a compilation unit's is no object reached by name.
    decl->in_compilation_unit = scope->in_compilation_unit;
    // §6.6.7: `nettype T1 T2;` declares T2 an alias of the nettype T1, which
    // writes no with clause of its own and resolves as T1 does. Detail 2: an
    // alias reaches the declaration it aliases, found here among those the
    // scope declared before it; detail 1: and the function T1 resolves with.
    for (auto* earlier : scope->children) {
      if (earlier->type == vpiNettypeDecl &&
          earlier->name == item.typedef_type.type_name) {
        decl->aliased = earlier;
        decl->nettype_with = earlier->nettype_with;
      }
    }
    scope->children.push_back(decl);

    // §37.23 detail 1: vpiWith answers NULL for a nettype declaration with no
    // resolution function. A declaration written
    // with one reaches the function the clause draws vpiWith to.
    if (!item.nettype_resolve_func.empty()) {
      name_pool_.emplace_back(item.nettype_resolve_func);
      auto* func = AllocObject();
      func->type = vpiFunction;
      func->name = name_pool_.back();
      func->parent = scope;
      // The function is reached through vpiWith and through nothing else: it is
      // not hung among the scope's children, because a scope's vpiFunction
      // iteration reports the functions the scope declares and §6.6.7 lets the
      // with clause name one declared in a package or a class instead.
      decl->nettype_with = func;
    }
  }
}

void VpiContext::AttachNettypeDeclarations(const RtlirDesign* design) {
  // §37.23 draws a "nettype decl" object carrying the declaration's name, the
  // resolution function its with clause names, and the nettype it aliases.
  // §37.10 detail 10: an instance's vpiNetTypedef iteration reaches the
  // nettypes it declares, so each declaration is an object of the scope it is
  // written in, an instance's or a package's, used by a net or not, and a net
  // of a package's nettype finds that nettype under the package alone.
  WalkInstanceObjects(design, object_map_,
                      [&](const RtlirModule* mod, const std::string& /*prefix*/,
                          VpiObject* scope) {
                        MakeNettypeDecls(
                            scope, ElementDeclNamed(*design, mod->name).items);
                      });
  if (design == nullptr) return;
  for (const PackageDecl* pkg : design->packages) {
    MakeNettypeDecls(DesignObjectForFlatName(pkg->name), pkg->items);
  }
  // §3.12.1: the compilation unit's own nettypes are its scope's, each unit's
  // where every file is one, "$unit#k", and the one unit's, "$unit", where
  // they are not; AttachPackages made the scope of a unit declaring one.
  const bool kOneUnit = design->compilation_units.empty();
  const std::size_t kUnits = kOneUnit ? 1 : design->compilation_units.size();
  for (std::size_t k = 0; k < kUnits; ++k) {
    const CompilationUnit* unit =
        kOneUnit ? design->compilation_unit : design->compilation_units[k];
    auto scope = object_map_.find(
        UnitScopes::ScopeName(kOneUnit ? -1 : static_cast<int>(k)));
    if (scope != object_map_.end())
      MakeNettypeDecls(scope->second, unit->cu_items);
  }
}

// Marks a top after the first, keyed under its own name as an instance is,
// as a top module, answering the tops so marked.
static std::unordered_set<const RtlirModule*> MarkKeyedTops(
    const RtlirDesign* design,
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  std::unordered_set<const RtlirModule*> keyed_tops;
  for (auto* top : design->top_modules) {
    if (top == nullptr || top == design->top_modules.front()) continue;
    auto named = objects.find(top->name);
    if (named == objects.end() || named->second == nullptr) continue;
    named->second->top_module = true;
    named->second->type = VpiInstanceKind(top);
    // §37.10: no instantiation names what a top is an instance of, which the
    // run records for every other instance; it is its own definition's.
    named->second->def_name = std::string(top->name);
    keyed_tops.insert(top);
  }
  return keyed_tops;
}

// The objects entered so far that no instance encloses and that are no top
// or package.
static std::vector<VpiObject*> UnenclosedObjects(
    const std::unordered_map<std::string_view, VpiObject*>& objects) {
  std::vector<VpiObject*> contents;
  for (const auto& [name, object] : objects) {
    // A package is enclosed by no module either, and stays so (§37.10).
    if (object != nullptr && object->parent == nullptr && !object->top_module &&
        object->type != vpiPackage) {
      contents.push_back(object);
    }
  }
  return contents;
}

void VpiContext::AttachTopModules(const RtlirDesign* design) {
  // §37.5 detail 1: the top-level modules are reached by vpi_iterate() with a
  // NULL reference object, which is where a PLI application walking a
  // design begins. Nothing built an object for a top module: the simulator keys
  // an instance's objects on a flat name and a top carries the empty prefix, so
  // what the passes above entered were the top's own contents under their bare
  // names and the top itself was an object of no kind. The iteration that
  // reaches the tops therefore reached none of them, VpiObject::top_module was
  // read by that filter and by vpi_get(vpiTopModule) and was written by
  // nothing, and walking a design through §37.1's data models had no first
  // step.
  if (design == nullptr) return;

  // A top after the first is keyed under its own name, as an instance is
  // (Lowerer::LowerParallelTop), so the object its contents were entered under
  // is already its module object; it is marked a top, and is none of the first
  // top's contents.
  std::unordered_set<const RtlirModule*> keyed_tops =
      MarkKeyedTops(design, object_map_);
  for (auto* top : design->top_modules) {
    if (top == nullptr || keyed_tops.contains(top)) continue;
    // The objects already entered under bare names are the top's contents, so
    // they become its children and it becomes their enclosing instance. They
    // stay keyed under those names, which is what the simulator keys their
    // storage on and what vpi_handle_by_name() has always answered to.
    std::vector<VpiObject*> contents = UnenclosedObjects(object_map_);

    name_pool_.emplace_back(top->name);
    auto* obj = AllocObject();
    obj->type = VpiInstanceKind(top);
    obj->name = name_pool_.back();
    obj->full_name = std::string(top->name);
    obj->def_name = std::string(top->name);
    obj->top_module = true;
    for (auto* object : contents) {
      object->parent = obj;
      obj->children.push_back(object);
      // The path each of these was entered under began below the top, so the
      // top is now a step of it that its vpiFullName does not name.
      PrefixFullNamesWithTop(object, obj->name);
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
  // §38.13: the time vpi_get_time reads is the run's, counted in the
  // simulation time unit, the design's global precision, which the
  // scheduler's ticks are.
  vpi.SetScheduler(&ctx.GetScheduler());
  vpi.SetSimTimeUnit(static_cast<int>(ctx.GlobalPrecision()));
  vpi.Attach(ctx, design);
  vpi.AttachDesignPorts(design);
  // §37.37: the paths run between the port objects the line above made, so they
  // are gathered once those exist.
  vpi.AttachDesignInterModPaths(design);
}

}  // namespace delta
