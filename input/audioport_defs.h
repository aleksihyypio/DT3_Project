#ifndef audioport_defs_h
#define audioport_defs_h

// Design parameters

//////////////////////////////////////////////////////////////////
// 1. Project parameters
//////////////////////////////////////////////////////////////////

#define student_number      "172320"
#define CLK_PERIOD          10.0
#define MCLK_PERIOD         54.25347222
#define FILTER_TAPS         53
#define AUDIO_FIFO_SIZE     60

//////////////////////////////////////////////////////////////////
// 2. Register counts for address computation
//////////////////////////////////////////////////////////////////

#define DSP_REGISTERS       106
#define AUDIOPORT_REGISTERS 111

//////////////////////////////////////////////////////////////////
// 3. Register indicec
//////////////////////////////////////////////////////////////////

#define CMD_REG_INDEX         0
#define STATUS_REG_INDEX      1
#define LEVEL_REG_INDEX       2
#define CFG_REG_INDEX         3
#define DSP_REGS_START_INDEX  4
#define DSP_REGS_END_INDEX    110
#define LEFT_FIFO_INDEX       111
#define RIGHT_FIFO_INDEX      171

//////////////////////////////////////////////////////////////////
// 4. Register addresses in APB address spaces
//////////////////////////////////////////////////////////////////   

#define AUDIOPORT_START_ADDRESS  0x8c000000   
#define AUDIOPORT_END_ADDRESS    0x8c0003A0   
#define CMD_REG_ADDRESS          0x8c000000   
#define STATUS_REG_ADDRESS       0x8c000004   
#define LEVEL_REG_ADDRESS        0x8c000008   
#define CFG_REG_ADDRESS          0x8c00000C   
#define DSP_REGS_START_ADDRESS   0x8c000010   
#define DSP_REGS_END_ADDRESS     0x8c0001B8   
#define LEFT_FIFO_ADDRESS        0x8c0001BC   
#define RIGHT_FIFO_ADDRESS       0x8c0002AC   

//////////////////////////////////////////////////////////////////
// 5. Useful Constants
//////////////////////////////////////////////////////////////////   

// a: Command register CMD_REG

#define CMD_NOP          0x0
#define CMD_CLR          0x1
#define CMD_CFG          0x2
#define CMD_START        0x4
#define CMD_STOP         0x8
#define CMD_LEVEL        0x10   
#define CMD_IRQACK       0x20   

// b: Status register STATUS_REG

#define STATUS_PLAY      0
#define STATUS_NODATA    1

// c: Configuration register CFG_REG   

// Config bit indices
#define CFG_FILTER      0

// Config bit values
#define DSP_FILTER_OFF  0
#define DSP_FILTER_ON   1

// d: Constants used in dsp_unit

#define DATABITS      24
#define COEFFBITS     32

// e: These are needed in the testbench

#define CLK_DIV_48000        (ceil((1000000000.0/48000.0)/(CLK_PERIOD)))

// g: dsp_unit max latency

#define DSP_UNIT_MAX_LATENCY  (ceil(double(CLK_DIV_48000)/16.0))

#endif
