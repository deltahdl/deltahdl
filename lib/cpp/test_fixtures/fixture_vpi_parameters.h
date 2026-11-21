#pragma once

#include <string>
#include <string_view>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

class ParametersOfEveryPlace : public VpiDesignRun {
 protected:
  static vpiHandle UnitScope() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }

  static vpiHandle Through(int relation, vpiHandle ref) {
    return ref == nullptr ? nullptr : vpi_handle(relation, ref);
  }

  static VpiObject* Reached(int relation, vpiHandle ref) {
    return VpiObjectOf(Through(relation, ref));
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static int Flag(int property, vpiHandle obj) {
    return obj == nullptr ? -1 : vpi_get(property, obj);
  }

  static std::string Str(int property, vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return text == nullptr ? "<null>" : text;
  }

  static int ValueOf(vpiHandle obj) {
    return obj == nullptr ? -1 : IntegerOf(obj);
  }

  static vpiHandle ParameterIn(vpiHandle scope, std::string_view name) {
    return scope == nullptr ? nullptr : Named(vpiParameter, scope, name);
  }

  static vpiHandle ParameterAt(const char* scope, std::string_view name) {
    return ParameterIn(By(scope), name);
  }
};

}  // namespace delta
