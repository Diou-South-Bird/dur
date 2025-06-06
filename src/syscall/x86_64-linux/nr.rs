/// A mapping of UArc syscalls to x86_64-linux syscalls.
/// `usize::MAX` means the syscall is unavailable for the platform.
pub const NRS: [usize; 420] = [
	60,
	0,
	1,
	3,
	5,
	8,
	59,
	39,
	165,
	105,
	102,
	101,
	162,
	74,
	62,
	32,
	163,
	16,
	72,
	109,
	121,
	95,
	161,
	110,
	112,
	160,
	93,
	98,
	96,
	164,
	167,
	169,
	10,
	11,
	76,
	77,
	91,
	140,
	141,
	137,
	138,
	36,
	38,
	61,
	179,
	80,
	81,
	73,
	26,
	19,
	20,
	124,
	149,
	150,
	151,
	152,
	131,
	40,
	106,
	104,
	107,
	108,
	113,
	114,
	115,
	116,
	27,
	28,
	41,
	53,
	49,
	42,
	50,
	55,
	54,
	51,
	52,
	44,
	46,
	45,
	47,
	48,
	64,
	66,
	29,
	31,
	30,
	67,
	69,
	70,
	68,
	71,
	219,
	57,
	2,
	85,
	86,
	87,
	133,
	90,
	37,
	34,
	132,
	21,
	82,
	83,
	84,
	22,
	100,
	12,
	166,
	136,
	33,
	111,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	170,
	88,
	89,
	134,
	9,
	103,
	4,
	6,
	212,
	153,
	168,
	99,
	usize::MAX,
	56,
	171,
	63,
	159,
	usize::MAX,
	174,
	175,
	176,
	177,
	139,
	135,
	183,
	122,
	123,
	78,
	23,
	75,
	156,
	142,
	143,
	144,
	145,
	24,
	146,
	147,
	148,
	35,
	25,
	178,
	7,
	180,
	157,
	15,
	13,
	14,
	127,
	128,
	129,
	130,
	17,
	18,
	79,
	125,
	126,
	58,
	97,
	92,
	94,
	117,
	118,
	119,
	120,
	155,
	217,
	187,
	188,
	189,
	190,
	191,
	192,
	193,
	194,
	195,
	196,
	197,
	198,
	199,
	186,
	200,
	202,
	203,
	204,
	234,
	206,
	207,
	208,
	209,
	210,
	231,
	213,
	233,
	232,
	218,
	221,
	222,
	223,
	224,
	225,
	226,
	227,
	228,
	229,
	230,
	usize::MAX,
	usize::MAX,
	216,
	237,
	239,
	238,
	240,
	241,
	242,
	243,
	244,
	245,
	246,
	248,
	249,
	250,
	247,
	251,
	252,
	253,
	254,
	255,
	256,
	257,
	258,
	259,
	260,
	261,
	263,
	264,
	265,
	266,
	267,
	268,
	269,
	270,
	271,
	272,
	273,
	274,
	275,
	276,
	278,
	279,
	309,
	281,
	235,
	285,
	280,
	282,
	284,
	283,
	286,
	287,
	289,
	290,
	294,
	293,
	292,
	291,
	295,
	296,
	297,
	298,
	300,
	301,
	302,
	303,
	304,
	305,
	306,
	308,
	310,
	311,
	312,
	313,
	314,
	315,
	316,
	317,
	318,
	319,
	321,
	322,
	323,
	324,
	299,
	307,
	43,
	288,
	325,
	326,
	327,
	328,
	332,
	333,
	334,
	329,
	330,
	331,
	424,
	425,
	426,
	427,
	428,
	429,
	430,
	431,
	432,
	433,
	434,
	435,
	436,
	437,
	438,
	439,
	440,
	441,
	442,
	443,
	444,
	445,
	446,
	448,
	449,
	450,
	451,
	452,
	453,
	454,
	455,
	456,
	457,
	458,
	459,
	460,
	461,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	172,
	173,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	181,
	182,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	154,
	usize::MAX,
	201,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	65,
	220,
	277,
	236,
	usize::MAX,
	320,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	usize::MAX,
	447,
];
