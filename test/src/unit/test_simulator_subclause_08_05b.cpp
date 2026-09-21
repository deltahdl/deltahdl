#include <gtest/gtest.h>

#include "helpers_scheduler.h"

namespace {

// §8.5 puts no restriction on a property's data type, and §7.2 declares a
// structure whose members are selected by name. A property declared with an
// unpacked struct typedef holds the structure as one value the width of the
// typedef's layout, so a member written through the handle lands in that
// member's bits and a member read through the handle comes out of them. The
// first member sits above the second in the layout, so losing it to a value
// narrower than the layout reads 12 rather than 312.
TEST(ObjectPropertySim,
     UnpackedStructPropertyMembersWrittenAndReadThroughAHandle) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.p.g = 12;\n"
                      "    out = c.p.f * 100 + c.p.g;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            312u);
}

// §8.11 lets a method name its object's property bare, so `p.f = x` inside a
// method writes the member of the structure the running object's `p` holds,
// and `p.f * 100 + p.g` reads both members back out of it. Dropping the write
// or reading the member as an undeclared name answers 0.
TEST(ObjectPropertySim, UnpackedStructPropertyMembersWrittenAndReadInMethods) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function void setf(int x); p.f = x; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "  function int sum(); return p.f * 100 + p.g; "
                      "endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.setf(7);\n"
                      "    c.setg(25);\n"
                      "    out = c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            725u);
}

// The two routes reach the same structure: a member written through the
// handle is read by a method, and a member written by a method is read
// through the handle. 3 from `c.p.f`, 12 from `c.p.g` and 15 from the method's
// sum make 3135; a member lost on either route changes each digit group.
TEST(ObjectPropertySim,
     UnpackedStructPropertyMemberWrittenThroughAHandleReadInAMethod) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function int sum(); return p.f + p.g; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.setg(12);\n"
                      "    out = c.p.f * 1000 + c.p.g * 10 + c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3135u);
}

// §8.5 puts no restriction on a property's data type and §26.3 references a
// package's declarations through the package scope resolution operator
// (printed pages 183 and 808 of IEEE 1800-2023), so `pk::sev_t s =
// pk::MED;` declares a property of the package's enum type holding the
// package's MED. The declaration was a parse error at the `::`. MED is 2 and
// HIGH 3, so the initializer read through the handle and the value written
// through it after make 23; a lost initializer reads 3 and a lost write 20.
TEST(ObjectPropertySim, PackageScopedEnumPropertyHoldsItsInitializer) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    out = c.s * 10;\n"
                      "    c.s = pk::HIGH;\n"
                      "    out = out + c.s;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            23u);
}

// A.2.7 gives a method's return type the same data_type, so a method returns
// `pk::sev_t` as a property is declared with it. `cur` returns the property
// as initialized (2), `top` writes HIGH into it and returns it (3), and `cur`
// then returns the written value (3): 233. A return type read as the method's
// class name leaves no method to call.
TEST(ObjectPropertySim, PackageScopedEnumReturnedByAMethod) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "  function pk::sev_t cur(); return s; endfunction\n"
                      "  function pk::sev_t top();\n"
                      "    s = pk::HIGH;\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    out = c.cur() * 100;\n"
                      "    out = out + c.top() * 10;\n"
                      "    out = out + c.cur();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            233u);
}

}  // namespace
