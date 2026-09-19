#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.26's own example: Fifo and Stack implement the parameterized interface
// classes PutImp and GetImp over a queue property `T myFifo[$:DEPTH-1]`
// (§7.10.5, §8.25), put pushing at the back and at the front respectively
// and get popping the front. Through PutImp#(int) handles, the Fifo gives
// back the 5 it was given first, the Stack the 6 it was given last, and the
// Fifo through a GetImp#(int) handle the 6 that remains. The bound DEPTH-1
// is the specialization's 3, which neither object's pushes reach.
TEST(InterfaceClassSim, FifoAndStackOverAQueuePropertyThroughInterfaceHandles) {
  EXPECT_EQ(RunAndGet("interface class PutImp#(type PUT_T = logic);\n"
                      "  pure virtual function void put(PUT_T a);\n"
                      "endclass\n"
                      "interface class GetImp#(type GET_T = logic);\n"
                      "  pure virtual function GET_T get();\n"
                      "endclass\n"
                      "class Fifo#(type T = logic, int DEPTH = 1)\n"
                      "    implements PutImp#(T), GetImp#(T);\n"
                      "  T myFifo[$:DEPTH-1];\n"
                      "  virtual function void put(T a);\n"
                      "    myFifo.push_back(a);\n"
                      "  endfunction\n"
                      "  virtual function T get();\n"
                      "    get = myFifo.pop_front();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Stack#(type T = logic, int DEPTH = 1)\n"
                      "    implements PutImp#(T), GetImp#(T);\n"
                      "  T myFifo[$:DEPTH-1];\n"
                      "  virtual function void put(T a);\n"
                      "    myFifo.push_front(a);\n"
                      "  endfunction\n"
                      "  virtual function T get();\n"
                      "    get = myFifo.pop_front();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    Fifo#(int, 4) f = new;\n"
                      "    Stack#(int, 4) s = new;\n"
                      "    PutImp#(int) pf, ps;\n"
                      "    GetImp#(int) gf;\n"
                      "    pf = f;\n"
                      "    ps = s;\n"
                      "    pf.put(5);\n"
                      "    pf.put(6);\n"
                      "    ps.put(5);\n"
                      "    ps.put(6);\n"
                      "    out = f.get() * 100 + s.get() * 10;\n"
                      "    gf = f;\n"
                      "    out = out + gf.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            566u);
}

}  // namespace
