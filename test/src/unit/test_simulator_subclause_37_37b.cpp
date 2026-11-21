#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class IntermodulePathsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle PortOf(const char* inst, const char* port) {
    return Named(vpiPort, By(inst), port);
  }

  static void PutRiseFall(vpiHandle path, double rise, double fall) {
    s_vpi_time times[2] = {};
    times[0].real = rise;
    times[1].real = fall;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiScaledRealTime;
    vpi_put_delays(path, &delay);
  }

  static std::vector<double> RiseFallOf(vpiHandle path) {
    s_vpi_time times[2] = {};
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiScaledRealTime;
    vpi_get_delays(path, &delay);
    return {times[0].real, times[1].real};
  }
};

constexpr const char* kFanout =
    "module drv(output [3:0] o); endmodule\n"
    "module rcv(input [3:0] i); endmodule\n"
    "module top;\n"
    "  wire [3:0] w;\n"
    "  drv a(.o(w));\n"
    "  rcv b(.i(w));\n"
    "  rcv e(.i(w));\n"
    "endmodule\n";

TEST_F(IntermodulePathsOfARun, EachInputAnOutputDrivesHasAPathOfItsOwn) {
  Run(kFanout);
  vpiHandle out = PortOf("top.a", "o");
  vpiHandle to_b = PortOf("top.b", "i");
  vpiHandle to_e = PortOf("top.e", "i");
  ASSERT_NE(out, nullptr);
  ASSERT_NE(to_b, nullptr);
  ASSERT_NE(to_e, nullptr);
  vpiHandle path_b = vpi_handle_multi(vpiInterModPath, out, to_b);
  vpiHandle path_e = vpi_handle_multi(vpiInterModPath, out, to_e);
  ASSERT_NE(path_b, nullptr);
  ASSERT_NE(path_e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, path_b), vpiInterModPath);
  EXPECT_EQ(vpi_compare_objects(path_b, path_e), 0);
}

TEST_F(IntermodulePathsOfARun, APathsPortsAreTheOutputAndTheInputItJoins) {
  Run(kFanout);
  vpiHandle out = PortOf("top.a", "o");
  vpiHandle to_e = PortOf("top.e", "i");
  const std::vector<vpiHandle> kPorts =
      ObjectsOf(vpiPort, vpi_handle_multi(vpiInterModPath, out, to_e));
  ASSERT_EQ(kPorts.size(), 2u);
  EXPECT_EQ(vpi_compare_objects(kPorts[0], out), 1);
  EXPECT_EQ(vpi_compare_objects(kPorts[1], to_e), 1);
  EXPECT_EQ(vpi_get(vpiSize, kPorts[1]), 4);
}

TEST_F(IntermodulePathsOfARun, EachPathKeepsTheDelaysPutToIt) {
  Run(kFanout);
  vpiHandle out = PortOf("top.a", "o");
  vpiHandle path_b =
      vpi_handle_multi(vpiInterModPath, out, PortOf("top.b", "i"));
  vpiHandle path_e =
      vpi_handle_multi(vpiInterModPath, out, PortOf("top.e", "i"));
  ASSERT_NE(path_b, nullptr);
  ASSERT_NE(path_e, nullptr);
  PutRiseFall(path_b, 3.0, 7.0);
  PutRiseFall(path_e, 4.0, 9.0);
  EXPECT_EQ(RiseFallOf(path_b), (std::vector<double>{3.0, 7.0}));
  EXPECT_EQ(RiseFallOf(path_e), (std::vector<double>{4.0, 9.0}));
}

}  // namespace
}  // namespace delta
