module case_stmt;
  logic [1:0] sel;

  initial begin
    sel = 0;
    case (sel)
      0: $display("zero");
      1: $display("one");
      default: $display("other");
    endcase

    sel = 1;
    case (sel)
      0: $display("zero");
      1: $display("one");
      default: $display("other");
    endcase

    sel = 3;
    case (sel)
      0: $display("zero");
      1: $display("one");
      default: $display("other");
    endcase
  end
endmodule
