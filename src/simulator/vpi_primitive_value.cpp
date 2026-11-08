#include "simulator/vpi_primitive_value.h"

#include <algorithm>
#include <vector>

#include "common/types.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiHandle ConnectedExpr(const VpiObject& term) {
  return term.children.empty() ? nullptr : term.children.front();
}

char StateBit(const Logic4Word& word) {
  if ((word.bval & 1) != 0) return 'x';
  return (word.aval & 1) != 0 ? '1' : '0';
}

}  // namespace

VpiHandle VpiPrimitiveValueSource(VpiHandle obj) {
  if (obj->type == vpiPrimTerm) return ConnectedExpr(*obj);
  if (!VpiIsPrimitiveType(obj->type)) return obj;
  const auto kDriven =
      std::ranges::find_if(obj->children, [](const VpiObject* term) {
        return term->type == vpiPrimTerm && term->direction != vpiInput;
      });
  return kDriven == obj->children.end() ? nullptr : ConnectedExpr(**kDriven);
}

bool VpiPutSequentialUdpValue(const VpiObject& obj, const s_vpi_value* value,
                              SimContext* sim) {
  if (sim == nullptr || obj.prim_type != vpiSeqPrim) return false;
  const auto kSetter = sim->UdpStateSetters().find(obj.run_key);
  if (kSetter == sim->UdpStateSetters().end()) return false;
  std::vector<Logic4Word> words;
  if (value != nullptr && VpiPutValueBits(*value, 1, words)) {
    kSetter->second(StateBit(words.front()));
  }
  return true;
}

}  // namespace delta
