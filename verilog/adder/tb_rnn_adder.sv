// Simulation test of rnn_adder against a reference bit-serial adder. A test, not the proof.
//
//   iverilog -g2012 -o tb_rnn_adder rnn_adder.sv tb_rnn_adder.sv && vvp tb_rnn_adder
`timescale 1ns / 1ps
module tb_rnn_adder;
    logic clk = 1'b0;
    logic reset = 1'b1;
    logic a = 1'b0;
    logic b = 1'b0;
    logic sum;
    logic carry;

    rnn_adder dut (.clk(clk), .reset(reset), .a(a), .b(b), .sum(sum), .carry(carry));

    always #5 clk = ~clk;

    integer errors = 0;
    integer checks = 0;
    integer n, t, run;
    integer code;
    integer seed = 1;
    logic c;  // the reference carry into the position being read

    // One clock edge with reset high, then reset low: the state is H0.
    task automatic do_reset;
        begin
            reset = 1'b1;
            @(posedge clk);
            #1;
            reset = 1'b0;
            c = 1'b0;
        end
    endtask

    // Apply one bit pair, check the settled outputs, clock it in.
    task automatic feed(input logic abit, input logic bbit);
        begin
            a = abit;
            b = bbit;
            #1;
            if (carry !== c) begin
                errors = errors + 1;
                $display("carry mismatch before the edge: got %b want %b", carry, c);
            end
            if (sum !== (abit ^ bbit ^ c)) begin
                errors = errors + 1;
                $display("sum mismatch: a=%b b=%b c=%b got %b", abit, bbit, c, sum);
            end
            checks = checks + 2;
            @(posedge clk);
            #1;
            c = (abit & bbit) | (abit & c) | (bbit & c);
        end
    endtask

    initial begin
        // Every input sequence of length 0 to 7.
        for (n = 0; n <= 7; n = n + 1) begin
            for (code = 0; code < (1 << (2 * n)); code = code + 1) begin
                do_reset();
                for (t = 0; t < n; t = t + 1) begin
                    feed(code[2 * t], code[2 * t + 1]);
                end
                if (carry !== c) begin
                    errors = errors + 1;
                    $display("final carry mismatch: length %0d code %0d", n, code);
                end
                checks = checks + 1;
            end
        end
        // 200 seeded streams of 1000 bit pairs.
        for (run = 0; run < 200; run = run + 1) begin
            do_reset();
            for (t = 0; t < 1000; t = t + 1) begin
                code = $random(seed);
                feed(code[0], code[1]);
            end
            if (carry !== c) begin
                errors = errors + 1;
                $display("final carry mismatch: random run %0d", run);
            end
            checks = checks + 1;
        end
        if (errors == 0) $display("ok: %0d checks, 0 errors", checks);
        else $display("FAIL: %0d checks, %0d errors", checks, errors);
        $finish;
    end
endmodule
