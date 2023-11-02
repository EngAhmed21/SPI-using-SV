module wrapper (wrapper_intf.DUT W_intf);
  localparam MEM_DEPTH = W_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

  logic clk, rst_n, SS_n, MOSI, rx_valid, tx_valid, MISO;
  logic [ADDR_SIZE - 1 : 0] tx_data;
  logic [ADDR_SIZE + 1 : 0] rx_data;

  slave_RAM_intf #(.MEM_DEPTH(MEM_DEPTH)) SR_intf (clk);

  assign clk            = W_intf.clk;
  assign rst_n          = W_intf.rst_n;
  assign SS_n           = W_intf.SS_n;
  assign MOSI           = W_intf.MOSI;
  assign W_intf.MISO    = MISO;  

  assign SR_intf.rst_n  = rst_n;
  assign tx_valid       = SR_intf.tx_valid;
  assign rx_valid       = SR_intf.rx_valid;
  assign tx_data        = SR_intf.tx_data;
  assign rx_data        = SR_intf.rx_data;

  slave SLAVE (.SS_n(SS_n), .MOSI(MOSI), .SR_intf(SR_intf), .MISO(MISO));
  RAM MEMORY (SR_intf);

  // Assertions for the internal signals
	`ifdef SIM_WRAPPER 
		// Check reset values
		always_comb begin
			if (!rst_n) begin
				wrap_rst_tx_valid_a:	assert final (tx_valid == 0);
				wrap_rst_rx_valid_a:	assert final (rx_valid == 0);
				wrap_rst_tx_data_a:   assert final (tx_data  == 0);
				wrap_rst_rx_data_a:	  assert final (rx_data  == 0);
			end
		end

    // Check rx_valid
    property wrap_rx_valid_pr;
      @(posedge clk) disable iff(!rst_n) (SS_n) ##1 (!SS_n) [*12] |=> (rx_valid);  
    endproperty
    wrap_rx_valid_a:	  assert property (wrap_rx_valid_pr);
		wrap_rx_valid_cov:  cover  property (wrap_rx_valid_pr);

    // Check tx_valid
    property wrap_tx_valid_pr;
      @(posedge clk) disable iff(!rst_n) (SS_n) ##1 (!SS_n) [*12] ##1 ((!SS_n) && 
       ({$past(MOSI, 10), $past(MOSI, 9)} == 2'b11)) |=> (tx_valid);  
    endproperty
    wrap_tx_valid_a:	  assert property (wrap_tx_valid_pr);
		wrap_tx_valid_cov:  cover  property (wrap_tx_valid_pr);

    // Check rx_data
    property wrap_rx_data_pr;
      @(posedge clk) disable iff(!rst_n) (SS_n) ##1 (!SS_n) [*12] |=> (rx_data == 
       {$past(MOSI, 10), $past(MOSI, 9), $past(MOSI, 8), $past(MOSI, 7), 
       $past(MOSI, 6), $past(MOSI, 5), $past(MOSI, 4), $past(MOSI, 3),
       $past(MOSI, 2), $past(MOSI)});  
    endproperty
    wrap_rx_data_a:	   assert property (wrap_rx_data_pr);
		wrap_rx_data_cov:  cover  property (wrap_rx_data_pr);
	`endif 
endmodule