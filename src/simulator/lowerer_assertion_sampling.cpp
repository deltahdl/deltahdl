#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

// §25.9 with §16.5.1: a dotted name that names no variable, `vif.d` or
// `m.vif.d`, reaches a member through a virtual interface bound only as the
// design runs, so the member it ends in is enrolled in every interface
// instance declaring it, whichever the handle comes to name.
// The instances are named from the top, and the scope reading the name,
// `scope_prefix`, is restored for the names after it.
void Lowerer::EnrollInterfaceMembers(std::string_view name,
                                     const std::string& scope_prefix) {
  auto dot = name.rfind('.');
  if (dot == std::string_view::npos) return;
  std::string_view member = name.substr(dot + 1);
  ctx_.SetLoweringInstancePrefix("");
  for (const std::string& prefix : interface_instance_prefixes_) {
    if (auto* var = ctx_.FindVariable(prefix + std::string(member))) {
      ctx_.AssertionSamples().Register(var, ctx_.GetArena());
    }
  }
  ctx_.SetLoweringInstancePrefix(scope_prefix);
}

namespace {

// The leaf elements of the dimensions `dim` onward under `prefix`, each
// index its declared one, outermost first: `arr[1][0]` for the element of
// `logic arr [1:0][1:0]` at 1 and 0.
void AppendLeafElements(const std::string& prefix,
                        const std::vector<uint32_t>& los,
                        const std::vector<uint32_t>& sizes, size_t dim,
                        std::vector<std::string>& out) {
  if (dim == los.size()) {
    out.push_back(prefix);
    return;
  }
  for (uint32_t i = 0; i < sizes[dim]; ++i) {
    AppendLeafElements(prefix + "[" + std::to_string(los[dim] + i) + "]", los,
                       sizes, dim + 1, out);
  }
}

}  // namespace

// §16.5.1 with §16.6: the elements of a fixed-size unpacked array a
// property reads are each a variable of their own, keyed by the array's name
// and the element's declared index in each dimension (TryArrayElementSelect
// and TryCompoundArraySelect in eval_select.cpp), so each is enrolled, a
// select read at a tick answering the element's Preponed value.
void Lowerer::EnrollArrayElements(const std::string& name) {
  const ArrayInfo* info = ctx_.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue) return;
  std::vector<std::string> elements;
  if (info->dim_sizes.empty()) {
    AppendLeafElements(name, {info->lo}, {info->size}, 0, elements);
  } else {
    AppendLeafElements(name, info->dim_los, info->dim_sizes, 0, elements);
  }
  for (const std::string& element : elements) {
    if (auto* var = ctx_.FindVariable(element)) {
      ctx_.AssertionSamples().Register(var, ctx_.GetArena());
    }
  }
}

void Lowerer::RegisterDesignAssertionSampling() {
  // §23.6 makes a hierarchical name an ordinary way to reach a variable, and
  // §16.5.1 puts no condition on where the variable a property reads is
  // declared, so `u.req` is enrolled exactly as a name the module declares
  // itself. That is why this runs after every module is lowered rather than
  // beside the process that named it: Lowerer::LowerChildModules creates an
  // instance's variables after the enclosing module's processes are lowered, so
  // a name resolved where it was found reached nothing and the read fell back
  // to the live value §16.5.1 exists to stop reading.
  //
  // Each name is resolved through SimContext::FindVariable under its own
  // instance prefix, which is the lookup the process body will make: no process
  // is executing here, so the prefix is the one SetLoweringInstancePrefix last
  // set, and the enrolled Variable* is therefore the one the read will find.
  for (const auto& scope : assertion_sample_scopes_) {
    ctx_.SetLoweringInstancePrefix(scope.inst_prefix);
    for (const auto& name : scope.names) {
      if (auto* var = ctx_.FindVariable(name)) {
        ctx_.AssertionSamples().Register(var, ctx_.GetArena());
      } else {
        EnrollInterfaceMembers(name, scope.inst_prefix);
      }
      EnrollArrayElements(name);
      // §16.6: a queue the property reads an element of is enrolled whole, so
      // the element read at a tick is the one sampled for it.
      if (auto* queue = ctx_.FindQueue(name)) {
        ctx_.AssertionSamples().RegisterQueue(queue, ctx_.GetArena());
      }
    }
  }
  ctx_.SetLoweringInstancePrefix("");
}

}  // namespace delta
