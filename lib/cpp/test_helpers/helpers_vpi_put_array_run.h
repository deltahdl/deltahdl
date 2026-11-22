#pragma once

#include <string>
#include <utility>
#include <vector>

#include "helpers_vpi_put_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

inline vpiHandle HandleNamed(const char* name) {
  return vpi_handle_by_name(VpiText(name), nullptr);
}

inline PLI_INT32 PutArrayAt(vpiHandle array, s_vpi_arrayvalue value,
                            std::vector<PLI_INT32> index, PLI_UINT32 num) {
  vpi_put_value_array(array, &value, index.data(), num);
  const PLI_INT32 kError = vpi_chk_error(nullptr);
  return kError;
}

inline PLI_INT32 PutIntsAt(vpiHandle array, std::vector<PLI_INT32> index,
                           std::vector<PLI_INT32> values,
                           PLI_UINT32 flags = 0) {
  s_vpi_arrayvalue value = {};
  value.format = vpiIntVal;
  value.flags = flags;
  value.value.integers = values.data();
  return PutArrayAt(array, value, std::move(index),
                    static_cast<PLI_UINT32>(values.size()));
}

inline PLI_INT32 PutInts(const char* name, std::vector<PLI_INT32> index,
                         std::vector<PLI_INT32> values, PLI_UINT32 flags = 0) {
  return PutIntsAt(HandleNamed(name), std::move(index), std::move(values),
                   flags);
}

inline PLI_INT32 PutOneInt(const char* name, PLI_INT32 integer, PLI_UINT32 num,
                           PLI_UINT32 flags) {
  s_vpi_arrayvalue value = {};
  value.format = vpiIntVal;
  value.flags = flags | vpiOneValue;
  value.value.integers = &integer;
  return PutArrayAt(HandleNamed(name), value, {0}, num);
}

inline std::string BitsNamed(const char* name) {
  s_vpi_value value = {};
  value.format = vpiBinStrVal;
  vpi_get_value(HandleNamed(name), &value);
  return value.value.str == nullptr ? "" : value.value.str;
}

inline int IntNamed(const char* name) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(HandleNamed(name), &value);
  return value.value.integer;
}

inline int IntAt(vpiHandle array, PLI_INT32 index) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_index(array, index), &value);
  return value.value.integer;
}

class ArrayPutsOfARun : public VpiPutRun {
 protected:
  static std::vector<int> IntsNamed(const std::vector<const char*>& names) {
    std::vector<int> values;
    values.reserve(names.size());
    for (const char* name : names) values.push_back(IntNamed(name));
    return values;
  }
};

}  // namespace delta
