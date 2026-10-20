#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

// One delivery of a simulation-event callback as its routine saw it: the
// reason, the name and type of the object in its obj field, whether it was
// given a value, the value's format and integer, the time it was given and
// the simulation time it ran at, and its index.
struct EventDelivery {
  int reason = 0;
  std::string obj;
  int obj_type = 0;
  bool has_value = false;
  int format = 0;
  int value = 0;
  uint32_t time = 0;
  uint32_t now = 0;
  int index = 0;
  bool operator==(const EventDelivery&) const = default;
};

inline std::vector<EventDelivery>& EventDeliveries() {
  static std::vector<EventDelivery> deliveries;
  return deliveries;
}

// What `$arm` does when the design calls it.
inline std::function<void()>& Armer() {
  static std::function<void()> armer;
  return armer;
}

inline PLI_INT32 RecordEventDelivery(p_cb_data cb) {
  EventDelivery d;
  d.reason = cb->reason;
  const char* name =
      cb->obj != nullptr ? vpi_get_str(vpiName, cb->obj) : nullptr;
  d.obj = name == nullptr ? "" : name;
  d.obj_type = cb->obj != nullptr ? vpi_get(vpiType, cb->obj) : 0;
  d.has_value = cb->value != nullptr;
  d.format = cb->value != nullptr ? cb->value->format : 0;
  d.value = cb->value != nullptr ? cb->value->value.integer : 0;
  d.time = cb->time != nullptr ? cb->time->low : 0;
  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  d.now = now.low;
  d.index = cb->index;
  EventDeliveries().push_back(d);
  return 0;
}

// Places a `reason` callback on `obj`, asking for the time as vpiSimTime
// and the value in `format`, vpiIntVal unless named.
inline vpiHandle PlaceEventCallback(int reason, vpiHandle obj,
                                    int format = vpiIntVal) {
  static s_vpi_time time;
  static std::deque<s_vpi_value> values;
  time.type = vpiSimTime;
  s_vpi_value& value = values.emplace_back();
  value.format = format;
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordEventDelivery;
  data.obj = obj;
  data.time = &time;
  data.value = &value;
  return vpi_register_cb(&data);
}

// A run whose design calls `$arm`, which places the case's callbacks once
// the model exists, its deliveries recorded.
class EventCallbacksOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    EventDeliveries().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$arm");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      Armer()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

// The deliveries recorded for `reason`, in order.
inline std::vector<EventDelivery> DeliveriesOf(int reason) {
  std::vector<EventDelivery> of;
  for (const EventDelivery& d : EventDeliveries()) {
    if (d.reason == reason) of.push_back(d);
  }
  return of;
}

inline vpiHandle TopObject(const char* name) {
  return vpi_handle_by_name(VpiText(name), nullptr);
}

}  // namespace delta
