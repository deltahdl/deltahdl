#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceClassDiamondSim, MergedParameterAndTypedefRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IntfBase; parameter SIZE = 64; endclass\n"
      "interface class IntfExt1 extends IntfBase; pure virtual function bit "
      "funcExt1(); endclass\n"
      "interface class IntfExt2 extends IntfBase; pure virtual function bit "
      "funcExt2(); endclass\n"
      "interface class IntfExt3 extends IntfExt1, IntfExt2; endclass\n"
      "class CD implements IntfExt1, IntfExt2;\n"
      "  virtual function bit funcExt1(); return 1; endfunction\n"
      "  virtual function bit funcExt2(); return 0; endfunction\n"
      "endclass\n"
      "interface class PB #(type T = int); pure virtual function bit "
      "funcBase(); endclass\n"
      "interface class PE1 extends PB#(bit); pure virtual function bit "
      "funcExt1(); endclass\n"
      "interface class PE2 extends PB#(logic); pure virtual function bit "
      "funcExt2(); endclass\n"
      "interface class PFinal extends PE1, PE2;\n"
      "  typedef bit T;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class PSame1 extends PB#(bit); endclass\n"
      "interface class PSame2 extends PB#(bit); endclass\n"
      "interface class PSameF extends PSame1, PSame2; endclass\n"
      "module m;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = IntfExt3::SIZE;\n"
      "    r2 = PSameF::T'(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 64u}, {"r2", 5u}});
}

}  // namespace
