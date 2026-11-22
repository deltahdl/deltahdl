#include <gtest/gtest.h>

#include <string>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct PathLookup {
  vpiHandle path = nullptr;
  PLI_INT32 error_level = 0;
};

class InterModPathOfARun : public VpiDesignRun {
 protected:
  static vpiHandle PortOf(const std::string& instance, const char* port) {
    return Named(vpiPort, By(instance), port);
  }

  static PathLookup Between(const std::string& out_instance,
                            const std::string& in_instance) {
    vpiHandle out_port = PortOf(out_instance, "o");
    vpiHandle in_port = PortOf(in_instance, "i");
    PathLookup lookup;
    if (out_port == nullptr || in_port == nullptr) return lookup;
    lookup.path = vpi_handle_multi(vpiInterModPath, out_port, in_port);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    lookup.error_level = kLevel;
    return lookup;
  }
};

TEST_F(InterModPathOfARun, AFannedOutOutputReachesAPathToEachInput) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module top; wire w; drv a(.o(w)); rcv b(.i(w)); rcv c(.i(w));\n"
      "  initial $noop; endmodule\n");
  const PathLookup kToB = Between("top.a", "top.b");
  const PathLookup kToC = Between("top.a", "top.c");
  ASSERT_NE(kToB.path, nullptr);
  ASSERT_NE(kToC.path, nullptr);
  EXPECT_EQ(vpi_get(vpiType, kToB.path), vpiInterModPath);
  EXPECT_EQ(vpi_get(vpiType, kToC.path), vpiInterModPath);
  EXPECT_EQ(vpi_compare_objects(kToB.path, kToC.path), 0);
}

TEST_F(InterModPathOfARun, VectorPortsOfOneSizeReachTheirPath) {
  Run("module drv(output [3:0] o); assign o = 4'h5; endmodule\n"
      "module rcv(input [3:0] i); endmodule\n"
      "module top; wire [3:0] w; drv a(.o(w)); rcv b(.i(w));\n"
      "  initial $noop; endmodule\n");
  const PathLookup kPath = Between("top.a", "top.b");
  ASSERT_NE(kPath.path, nullptr);
  EXPECT_EQ(vpi_get(vpiType, kPath.path), vpiInterModPath);
  EXPECT_EQ(kPath.error_level, 0);
}

TEST_F(InterModPathOfARun, PortsOfDifferentSizesAreAnError) {
  Run("module drv(output [7:0] o); assign o = 8'h5a; endmodule\n"
      "module rcv(input [3:0] i); endmodule\n"
      "module top; wire [7:0] w; drv a(.o(w)); rcv b(.i(w));\n"
      "  initial $noop; endmodule\n");
  const PathLookup kPath = Between("top.a", "top.b");
  EXPECT_EQ(kPath.path, nullptr);
  EXPECT_EQ(kPath.error_level, vpiError);
}

TEST_F(InterModPathOfARun, DISABLED_PortsAtDifferentDepthsReachTheirPath) {
  Run("module drv(output o); assign o = 1'b1; endmodule\n"
      "module rcv(input i); endmodule\n"
      "module wrap(input i); rcv r(.i(i)); endmodule\n"
      "module top; wire w; drv a(.o(w)); wrap p(.i(w));\n"
      "  initial $noop; endmodule\n");
  ASSERT_NE(PortOf("top.p.r", "i"), nullptr);
  ASSERT_NE(PortOf("top.a", "o"), nullptr);
  const PathLookup kPath = Between("top.a", "top.p.r");
  ASSERT_NE(kPath.path, nullptr);
  EXPECT_EQ(vpi_get(vpiType, kPath.path), vpiInterModPath);
  EXPECT_EQ(kPath.error_level, 0);
}

}  // namespace
}  // namespace delta
