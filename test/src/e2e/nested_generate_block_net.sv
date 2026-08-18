// IEEE 1800-2023 §23.9: an identifier "referenced directly (without a
// hierarchical path) within a task, function, named block, or generate block
// ... shall be declared either within the task, function, named block, or
// generate block locally or within a module, interface, program, checker, task,
// function, named block, or generate block that is higher in the same branch of
// the name tree", and "the search shall continue upward until an item by that
// name is found or until a module, interface, program, or checker boundary is
// encountered". Block b is higher in the same branch than block a, so the w
// that a writes is the w that b declared.
//
// §27.4 makes each of them "a separate scope and a new level of hierarchy when
// it is instantiated", so a lookup that tries only the innermost block and then
// the module skips b entirely. Where the reference is on the left of a
// continuous assignment or in a terminal list, §6.10 then assumes an implicit
// net for it, and the source drives a second w that nothing reads.
//
// The write and the read stand in different blocks and at different times: a
// writes at time 0 and b reads at time 1, so the value printed is one that
// crossed the block boundary rather than one either block could have produced
// alone.
module nested_generate_block_net;
  generate
    if (1) begin : b
      logic w;

      if (1) begin : a
        initial w = 1'b1;
      end

      initial begin
        #1;
        $display("%0d", w);
      end
    end
  endgenerate
endmodule
