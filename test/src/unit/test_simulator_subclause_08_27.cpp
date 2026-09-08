#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassSim, ForwardTypedefMutualReferenceAssignment) {
  EXPECT_EQ(RunAndGet("typedef class C2;\n"
                      "class C1;\n"
                      "  C2 c;\n"
                      "  int x;\n"
                      "endclass\n"
                      "class C2;\n"
                      "  C1 c;\n"
                      "  int y;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C1 a;\n"
                      "    C2 b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.c = b;\n"
                      "    b.c = a;\n"
                      "    a.x = 10;\n"
                      "    b.y = 20;\n"
                      "    result = a.x + b.c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(ClassSim, ForwardTypedefSelfReferentialLinkedList) {
  EXPECT_EQ(RunAndGet("typedef class Node;\n"
                      "class Node;\n"
                      "  Node next;\n"
                      "  int data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Node a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.data = 1;\n"
                      "    b.data = 2;\n"
                      "    a.next = b;\n"
                      "    result = a.next.data;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

// §8.27: a forward typedef may refer to a class that has a parameter port list.
// End-to-end via §8.25's real parameterized-class syntax: forward-declare C,
// then refer to it with a positional parameter override and read the override
// value back at runtime, confirming the forward-declared name resolves to the
// parameterized class.
TEST(ClassSim, ForwardTypedefParameterizedClassPositionalOverride) {
  EXPECT_EQ(RunAndGet("typedef class C;\n"
                      "class C #(parameter int p = 2);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#(5)::p;\n"
                      "endmodule\n",
                      "result"),
            5u);
}

// §8.27: the same forward-declared parameterized class, referred to with a
// named parameter override, resolves and reads back the named override value.
TEST(ClassSim, ForwardTypedefParameterizedClassNamedOverride) {
  EXPECT_EQ(RunAndGet("typedef class C;\n"
                      "class C #(parameter int p = 2, type T = int);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#(.p(9))::p;\n"
                      "endmodule\n",
                      "result"),
            9u);
}

// §8.3 makes a class variable a handle to an object, and §8.27's forward
// declaration says nothing about its width -- the name is introduced before the
// type. The elaborated table recorded one bit for it, which is §6.10's answer
// for the implicit type a forward declaration leaves behind, and every reader
// of that table that does not ask separately whether the name is a class
// inherits it: a handle truncated to a bit is a handle to nothing.
//
// The handle is carried through a subroutine formal and a body local here
// because those are the two declarations sized from that table, and both are
// written on a class the file forward-declares, which is the only way the 1 was
// ever recorded. Reading a property back through the local is what says the
// handle survived.
TEST(ClassSim, ForwardTypedefHandleSurvivesASubroutineFormalAndLocal) {
  EXPECT_EQ(RunAndGet("typedef class C;\n"
                      "class C;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  function automatic int read_x(C h);\n"
                      "    C held;\n"
                      "    held = h;\n"
                      "    return held.x;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.x = 42;\n"
                      "    result = read_x(c);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

}  // namespace
