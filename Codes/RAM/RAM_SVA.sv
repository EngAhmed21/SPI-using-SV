module RAM_SVA (slave_RAM_intf.RAM intf);
    localparam MEM_DEPTH = SR_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	logic clk, rst_n, rx_valid, tx_valid;
	logic [ADDR_SIZE + 1 : 0] din;
    logic [ADDR_SIZE - 1 : 0] dout, wr_addr, rd_addr;
    logic [ADDR_SIZE - 1 : 0] mem_test [MEM_DEPTH];

	assign clk 				= intf.clk;
	assign rst_n 			= intf.rst_n;
	assign rx_valid 		= intf.rx_valid;
	assign din 				= intf.rx_data;
	assign dout 		    = intf.tx_data;
	assign tx_valid 	    = intf.tx_valid;

    // Check the reset values
    always_comb begin
        if (!rst_n) begin
            rstn_dout_a:  assert final (~(|dout));
            rstn_tx_a:    assert final (!tx_valid);
        end
    end

    // Check the value of tx_valid when the operation is read data
    property rd_data_tx_pr;
        @(posedge clk) disable iff(!rst_n) ((rx_valid) && (&(din [ADDR_SIZE + 1 : ADDR_SIZE]))) |=> (tx_valid);
    endproperty
    rd_data_tx_a:         assert property (rd_data_tx_pr);
    rd_data_tx_cov:       cover  property (rd_data_tx_pr);

    // Check the value of tx_valid when the operation isn't read data 
    property not_rd_data_tx_pr;
        @(posedge clk) disable iff(!rst_n) ((rx_valid) && (!(&(din [ADDR_SIZE + 1 : ADDR_SIZE])))) |=> (!tx_valid);
    endproperty
    not_rd_data_tx_a:    assert property (not_rd_data_tx_pr);
    not_rd_data_tx_cov:  cover  property (not_rd_data_tx_pr);

    // Check dout when the operation is read data
    property rd_data_dout_pr;
        @(posedge clk) disable iff(!rst_n) ((rx_valid) && (&(din [ADDR_SIZE + 1 : ADDR_SIZE]))) |=> (dout === $past(mem_test [$past(rd_addr)]));
    endproperty
    rd_data_dout_a:      assert property (rd_data_dout_pr);
    rd_data_dout_cov:    cover  property (rd_data_dout_pr);

    // Check that the value of dout doesn't change if the operation isn't read data
    property no_change_dout_pr;
        @(posedge clk) disable iff(!rst_n) ((!rx_valid) || (!(&(din [ADDR_SIZE + 1 : ADDR_SIZE])))) |=> (dout === $past(dout));
    endproperty
    no_change_dout_a:     assert property (no_change_dout_pr);
    no_change_dout_cov:   cover  property (no_change_dout_pr);

    // Reference
    initial begin
        $readmemh("RAM_data.dat", mem_test, 0, 255);
    end
    always_comb begin
        if (!rst_n) begin
            wr_addr = 0;
            rd_addr = 0;
        end
        else if (rx_valid) 
            case (din [ADDR_SIZE + 1 : ADDR_SIZE])
                2'b00:  wr_addr            = din [ADDR_SIZE - 1 : 0];
                2'b01:  mem_test [wr_addr] = din [ADDR_SIZE - 1 : 0];
                2'b10:  rd_addr            = din [ADDR_SIZE - 1 : 0];
            endcase
    end
endmodule