#include "LostCoins.h"
#include "Base58.h"
#include "Bech32.h"
#include "hash/sha512.h"
#include "IntGroup.h"
#include "Timer.h"
#include "hash/ripemd160.h"
#include <cstring>
#include <cmath>
#include <stdexcept>
#include <cassert>
#include <algorithm>
#include <iostream>

#include <string>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include "hash/sha256.h"
#include <sstream>
#include <stdlib.h>
#include <windows.h>
#include <conio.h>

#include <vector>
#include <random>
#include <ctime>
#include <iomanip>

#include <atomic>
#include <mutex>
#include <thread>
#include <fstream>
#include <iterator>
#include <regex>
#include "includeAll.h"


#include "bip39/bip39.h"
#include "dictionary/english.h"
#include "dictionary/spanish.h"
#include "dictionary/japanese.h"
#include "dictionary/italian.h"
#include "dictionary/french.h"
#include "dictionary/korean.h"
#include "dictionary/chinese_simplified.h"
#include "dictionary/chinese_traditional.h"

#include "picosha2.h"

#include <vector>
#include <random>
#include <climits>
#include <algorithm>
#include <functional>
#include <cassert>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <array>
#include <cstring>

unsigned char master_node[NODE_LENGTH];
using namespace std;

#ifndef WIN64
#include <pthread.h>
#endif

using namespace std;

Point Gn[CPU_GRP_SIZE / 2];
Point _2Gn;

// ----------------------------------------------------------------------------

LostCoins::LostCoins(string addressFile, string seed, string zez, int diz, int searchMode,
	bool useGpu, string outputFile, bool useSSE, uint32_t maxFound,
	uint64_t rekey, int nbit, int nbit2, bool paranoiacSeed, const std::string& rangeStart1, const std::string& rangeEnd1, bool& should_exit)
{
	this->searchMode = searchMode;
	this->useGpu = useGpu;
	this->outputFile = outputFile;
	this->useSSE = useSSE;
	this->nbGPUThread = 0;
	this->addressFile = addressFile;
	this->rekey = rekey;
	this->nbit = nbit;
	this->nbit2 = nbit2;
	this->maxFound = maxFound;
	this->seed = seed;
	this->zez = zez;
	this->diz = diz;
	this->searchType = P2PKH;
	this->rangeStart1;
	this->rangeEnd1;
	this->rangeDiff;
	secp = new Secp256K1();
	secp->Init();
	
	// load address file
	uint8_t buf[20];
	FILE* wfd;
	uint64_t N = 0;

	wfd = fopen(this->addressFile.c_str(), "rb");
	if (!wfd) {
		printf("%s can not open\n", this->addressFile.c_str());
		exit(1);
	}

	_fseeki64(wfd, 0, SEEK_END);
	N = _ftelli64(wfd);
	N = N / 20;
	rewind(wfd);

	DATA = (uint8_t*)malloc(N * 20);
	memset(DATA, 0, N * 20);

	bloom = new Bloom(2 * N, 0.000001);

	if (N > 100) {
		uint64_t percent = (N - 1) / 100;
		uint64_t i = 0;
		printf("\n");
		while (i < N && !should_exit) {
			memset(buf, 0, 20);
			memset(DATA + (i * 20), 0, 20);
			if (fread(buf, 1, 20, wfd) == 20) {
				bloom->add(buf, 20);
				memcpy(DATA + (i * 20), buf, 20);
				if (i % percent == 0) {
					printf("\r Loading      : %llu %%", (i / percent));
					fflush(stdout);
				}
			}
			i++;
		}
		printf("\n");
		fclose(wfd);

		if (should_exit) {
			delete secp;
			delete bloom;
			if (DATA)
				free(DATA);
			exit(0);
		}

		BLOOM_N = bloom->get_bytes();
		TOTAL_ADDR = N;
		printf(" Loaded       : %s address\n", formatThousands(i).c_str());
		printf("\n");

		bloom->print();
		printf("\n");

		lastRekey = 0;
	
	
	}
	else {
		uint64_t percent = N;
		uint64_t i = 0;
		printf("\n");
		while (i < N && !should_exit) {
			memset(buf, 0, 20);
			memset(DATA + (i * 20), 0, 20);
			if (fread(buf, 1, 20, wfd) == 20) {
				bloom->add(buf, 20);
				memcpy(DATA + (i * 20), buf, 20);
				
				printf("\r Loading      : %d address", N);
				fflush(stdout);
				
			}
			i++;
		}
		printf("\n");
		fclose(wfd);

		if (should_exit) {
			delete secp;
			delete bloom;
			if (DATA)
				free(DATA);
			exit(0);
		}

		BLOOM_N = bloom->get_bytes();
		TOTAL_ADDR = N;
		printf(" Loaded       : %s address\n", formatThousands(i).c_str());
		printf("\n");

		bloom->print();
		printf("\n");

		lastRekey = 0;
	}

	

	// Compute Generator table G[n] = (n+1)*G

	Point g = secp->G;
	Gn[0] = g;
	g = secp->DoubleDirect(g);
	Gn[1] = g;
	for (int i = 2; i < CPU_GRP_SIZE / 2; i++) {
		g = secp->AddDirect(g, secp->G);
		Gn[i] = g;
	}
	// _2Gn = CPU_GRP_SIZE*G
	_2Gn = secp->DoubleDirect(Gn[CPU_GRP_SIZE / 2 - 1]);

	// Constant for endomorphism
	// if a is a nth primitive root of unity, a^-1 is also a nth primitive root.
	// beta^3 = 1 mod p implies also beta^2 = beta^-1 mop (by multiplying both side by beta^-1)
	// (beta^3 = 1 mod p),  beta2 = beta^-1 = beta^2
	// (lambda^3 = 1 mod n), lamba2 = lamba^-1 = lamba^2
	beta.SetBase16("7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee");
	lambda.SetBase16("5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72");
	beta2.SetBase16("851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40");
	lambda2.SetBase16("ac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce");
	
	char *ctimeBuff;
	time_t now = time(NULL);
	ctimeBuff = ctime(&now);
	printf("  Start Time  : %s", ctimeBuff);
	

	if (rekey == 0) {
		printf("\n  TEST Mode   : %.0f ", (double)rekey);
		printf("\n  Mode BIP    : BIP39 -> Bip32 -> Bip44 ");
		printf("\n  Language    : %s ", seed.c_str());
		printf("\n  Use words   : %s ", zez.c_str());
		printf("\n  Check       : %d addresses for each account ", nbit);
		printf("\n  Site        : https://github.com/phrutis/BIP39  \n  Donate      : bc1qh2mvnf5fujg93mwl8pe688yucaw9sflmwsukz9 \n\n");
		
	}
	if (rekey == 1) {
		printf("\n  Mode BIP    : BIP39 -> Bip32 -> Bip44 ");
		printf("\n  Language    : %s ", seed.c_str());
		printf("\n  Use words   : %s ", zez.c_str());
		printf("\n  Check       : %d addresses for each account ", nbit);
		printf("\n  BIP32       : Account 0 m/0/0 -> m/0/%d", nbit);
		printf("\n  BIP32       : Account 1 m/1/0 -> m/1/%d", nbit);
		printf("\n  BIP44       : Account 0 External 0 m/44'/0'/0'/0/0 -> m/44'/0'/0'/0/%d", nbit);
		printf("\n  BIP44       : Account 0 External 1 m/44'/0'/0'/1/0 -> m/44'/0'/0'/1/%d", nbit);
		printf("\n  BIP44       : Account 1 External 0 m/44'/0'/1'/0/0 -> m/44'/0'/1'/0/%d", nbit);
		printf("\n  BIP44       : Account 1 External 1 m/44'/0'/1'/1/0 -> m/44'/0'/1'/1/%d", nbit);
		printf("\n  Site        : https://github.com/phrutis/BIP39 \n  Donate      : bc1qh2mvnf5fujg93mwl8pe688yucaw9sflmwsukz9 \n\n");


	}
	if (rekey > 2) {
		printf("\n  ERROR!!! \n  Check -r ? \n  Range -r from 1 - 8\n  BYE   \n\n");
		exit(-1);

	}
	

}

LostCoins::~LostCoins()
{
	delete secp;
	delete bloom;
	if (DATA)
		free(DATA);
}

// ----------------------------------------------------------------------------

double log1(double x)
{
	// Use taylor series to approximate log(1-x)
	return -x - (x * x) / 2.0 - (x * x * x) / 3.0 - (x * x * x * x) / 4.0;
}

void LostCoins::output(string addr, string pAddr, string pAddrHex)
{

#ifdef WIN64
	WaitForSingleObject(ghMutex, INFINITE);
#else
	pthread_mutex_lock(&ghMutex);
#endif

	FILE *f = stdout;
	bool needToClose = false;

	if (outputFile.length() > 0) {
		f = fopen(outputFile.c_str(), "a");
		if (f == NULL) {
			printf("Cannot open %s for writing\n", outputFile.c_str());
			f = stdout;
		}
		else {
			needToClose = true;
		}
	}

	if (!needToClose)
	printf("\n");
	fprintf(f, "* PubAddress: %s \n", addr.c_str());

	//if (startPubKeySpecified) {

	//	fprintf(f, "PartialPriv: %s\n", pAddr.c_str());

	//}
	//else
	{

		switch (searchType) {
		case P2PKH:
			fprintf(f, "* Priv (WIF): p2pkh: %s \n", pAddr.c_str());
			break;
		case P2SH:
			fprintf(f, "* Priv (WIF): p2wpkh-p2sh: %s \n", pAddr.c_str());
			break;
		case BECH32:
			fprintf(f, "* Priv (WIF): p2wpkh: %s \n", pAddr.c_str());
			break;
		}
		fprintf(f, "* Priv (HEX): %s\n", pAddrHex.c_str());

	}
	HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
	SetConsoleTextAttribute(hConsole, FOREGROUND_BLUE | FOREGROUND_GREEN | FOREGROUND_INTENSITY);

	printf("\n  =================================================================================");
	printf("\n  * PubAddress: %s ", addr.c_str());
	printf("\n  * Priv(WIF) : p2pkh: %s ", pAddr.c_str());
	printf("\n  * Priv(HEX) : %s ", pAddrHex.c_str());
	printf("\n  ===================================================================================\n");
	if (needToClose)
		fclose(f);

#ifdef WIN64
	ReleaseMutex(ghMutex);
#else
	pthread_mutex_unlock(&ghMutex);
#endif

}

// ----------------------------------------------------------------------------

bool LostCoins::checkPrivKey(string addr, Int &key, int32_t incr, int endomorphism, bool mode)
{

	Int k(&key);
	//Point sp = startPubKey;

	if (incr < 0) {
		k.Add((uint64_t)(-incr));
		k.Neg();
		k.Add(&secp->order);
		//if (startPubKeySpecified)
		//	sp.y.ModNeg();
	}
	else {
		k.Add((uint64_t)incr);
	}

	// Endomorphisms
	switch (endomorphism) {
	case 1:
		k.ModMulK1order(&lambda);
		//if (startPubKeySpecified)
		//	sp.x.ModMulK1(&beta);
		break;
	case 2:
		k.ModMulK1order(&lambda2);
		//if (startPubKeySpecified)
		//	sp.x.ModMulK1(&beta2);
		break;
	}

	// Check addresses
	Point p = secp->ComputePublicKey(&k);
	//if (startPubKeySpecified)
	//	p = secp->AddDirect(p, sp);

	string chkAddr = secp->GetAddress(searchType, mode, p);
	if (chkAddr != addr) {

		//Key may be the opposite one (negative zero or compressed key)
		k.Neg();
		k.Add(&secp->order);
		p = secp->ComputePublicKey(&k);
		//if (startPubKeySpecified) {
		//	sp.y.ModNeg();
		//	p = secp->AddDirect(p, sp);
		//}
		string chkAddr = secp->GetAddress(searchType, mode, p);
		if (chkAddr != addr) {
			printf("\n  Check your text file for junkand scribbles\n");
			printf("  Warning, wrong private key generated !\n");
			printf("  Addr :%s\n", addr.c_str());
			printf("  Check:%s\n", chkAddr.c_str());
			printf("  Endo:%d incr:%d comp:%d\n", endomorphism, incr, mode);
			//return false;
		}

	}

	output(addr, secp->GetPrivAddress(mode, k), k.GetBase16());

	return true;

}

// ----------------------------------------------------------------------------

#ifdef WIN64
DWORD WINAPI _FindKey(LPVOID lpParam)
{
#else
void *_FindKey(void *lpParam)
{
#endif
	TH_PARAM *p = (TH_PARAM *)lpParam;
	p->obj->FindKeyCPU(p);
	return 0;
}

#ifdef WIN64
DWORD WINAPI _FindKeyGPU(LPVOID lpParam)
{
#else
void *_FindKeyGPU(void *lpParam)
{
#endif
	TH_PARAM *p = (TH_PARAM *)lpParam;
	p->obj->FindKeyGPU(p);
	return 0;
}

// ----------------------------------------------------------------------------

void LostCoins::checkAddresses(bool compressed, Int key, int i, Point p1)
{
	unsigned char h0[20];
	Point pte1[1];
	Point pte2[1];

	// Point
	secp->GetHash160(searchType, compressed, p1, h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i, 0, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #1
	pte1[0].x.ModMulK1(&p1.x, &beta);
	pte1[0].y.Set(&p1.y);
	secp->GetHash160(searchType, compressed, pte1[0], h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i, 1, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #2
	pte2[0].x.ModMulK1(&p1.x, &beta2);
	pte2[0].y.Set(&p1.y);
	secp->GetHash160(searchType, compressed, pte2[0], h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i, 2, compressed)) {
			nbFoundKey++;
		}
	}

	// Curve symetrie
	// if (x,y) = k*G, then (x, -y) is -k*G
	p1.y.ModNeg();
	secp->GetHash160(searchType, compressed, p1, h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -i, 0, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #1
	pte1[0].y.ModNeg();
	secp->GetHash160(searchType, compressed, pte1[0], h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -i, 1, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #2
	pte2[0].y.ModNeg();
	secp->GetHash160(searchType, compressed, pte2[0], h0);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -i, 2, compressed)) {
			nbFoundKey++;
		}
	}
}

// ----------------------------------------------------------------------------

void LostCoins::checkAddressesSSE(bool compressed, Int key, int i, Point p1, Point p2, Point p3, Point p4)
{
	unsigned char h0[20];
	unsigned char h1[20];
	unsigned char h2[20];
	unsigned char h3[20];
	Point pte1[4];
	Point pte2[4];

	// Point -------------------------------------------------------------------------
	secp->GetHash160(searchType, compressed, p1, p2, p3, p4, h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i + 0, 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, i + 1, 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, i + 2, 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, i + 3, 0, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #1
	// if (x, y) = k * G, then (beta*x, y) = lambda*k*G
	pte1[0].x.ModMulK1(&p1.x, &beta);
	pte1[0].y.Set(&p1.y);
	pte1[1].x.ModMulK1(&p2.x, &beta);
	pte1[1].y.Set(&p2.y);
	pte1[2].x.ModMulK1(&p3.x, &beta);
	pte1[2].y.Set(&p3.y);
	pte1[3].x.ModMulK1(&p4.x, &beta);
	pte1[3].y.Set(&p4.y);

	secp->GetHash160(searchType, compressed, pte1[0], pte1[1], pte1[2], pte1[3], h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i + 0, 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, i + 1, 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, i + 2, 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, i + 3, 1, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #2
	// if (x, y) = k * G, then (beta2*x, y) = lambda2*k*G
	pte2[0].x.ModMulK1(&p1.x, &beta2);
	pte2[0].y.Set(&p1.y);
	pte2[1].x.ModMulK1(&p2.x, &beta2);
	pte2[1].y.Set(&p2.y);
	pte2[2].x.ModMulK1(&p3.x, &beta2);
	pte2[2].y.Set(&p3.y);
	pte2[3].x.ModMulK1(&p4.x, &beta2);
	pte2[3].y.Set(&p4.y);

	secp->GetHash160(searchType, compressed, pte2[0], pte2[1], pte2[2], pte2[3], h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, i + 0, 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, i + 1, 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, i + 2, 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, i + 3, 2, compressed)) {
			nbFoundKey++;
		}
	}

	// Curve symetrie -------------------------------------------------------------------------
	// if (x,y) = k*G, then (x, -y) is -k*G

	p1.y.ModNeg();
	p2.y.ModNeg();
	p3.y.ModNeg();
	p4.y.ModNeg();

	secp->GetHash160(searchType, compressed, p1, p2, p3, p4, h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -(i + 0), 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, -(i + 1), 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, -(i + 2), 0, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, -(i + 3), 0, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #1
	// if (x, y) = k * G, then (beta*x, y) = lambda*k*G
	pte1[0].y.ModNeg();
	pte1[1].y.ModNeg();
	pte1[2].y.ModNeg();
	pte1[3].y.ModNeg();

	secp->GetHash160(searchType, compressed, pte1[0], pte1[1], pte1[2], pte1[3], h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -(i + 0), 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, -(i + 1), 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, -(i + 2), 1, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, -(i + 3), 1, compressed)) {
			nbFoundKey++;
		}
	}

	// Endomorphism #2
	// if (x, y) = k * G, then (beta2*x, y) = lambda2*k*G
	pte2[0].y.ModNeg();
	pte2[1].y.ModNeg();
	pte2[2].y.ModNeg();
	pte2[3].y.ModNeg();

	secp->GetHash160(searchType, compressed, pte2[0], pte2[1], pte2[2], pte2[3], h0, h1, h2, h3);
	if (CheckBloomBinary(h0) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h0);
		if (checkPrivKey(addr, key, -(i + 0), 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h1) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h1);
		if (checkPrivKey(addr, key, -(i + 1), 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h2) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h2);
		if (checkPrivKey(addr, key, -(i + 2), 2, compressed)) {
			nbFoundKey++;
		}
	}
	if (CheckBloomBinary(h3) > 0) {
		string addr = secp->GetAddress(searchType, compressed, h3);
		if (checkPrivKey(addr, key, -(i + 3), 2, compressed)) {
			nbFoundKey++;
		}
	}
}

void bigPrintVariableSize(const uint8_tt* number, const unsigned int size, const bool is_big_endian)
{
	unsigned int i;
	if (is_big_endian)
	{
		for (i = 0; i < size; i++)
		{
			printf("%02x", number[i]);
			
		}
	}
	else
	{
		for (i = (uint8_tt)(size - 1); i < size; i--)
		{
			printf("%02x", number[i]);
		}
	}
}
void printLittleEndian32(const BigNum256 buffer)
{
	bigPrintVariableSize(buffer, 32, false);
}

void fillWithRandom(uint8_t* out, unsigned int len)
{
	unsigned int i;

	for (i = 0; i < len; i++)
	{
		out[i] = 0;//(uint8_t)rand();wangnandebug
	}
}

// ----------------------------------------------------------------------------
void LostCoins::getCPUStartingKey(int thId, Int &key, Point &startP)
{

}


void LostCoins::FindKeyCPU(TH_PARAM* ph)
{

	if (rekey == 0) {
		int thId = ph->threadId;
		counters[thId] = 0;

		IntGroup* grp = new IntGroup(CPU_GRP_SIZE / 1024 + 1);

		Int  key;
		Point startP;
		getCPUStartingKey(thId, key, startP);

		Int dx[CPU_GRP_SIZE / 1024 + 1];
		Point pts[CPU_GRP_SIZE];

		Int dy;
		Int dyn;
		Int _s;
		Int _p;
		Point pp;
		Point pn;
		grp->Set(dx);

		ph->hasStarted = true;
		ph->rekeyRequest = false;
		while (1 < 2) {
			akk += 1;
			uint8_t seed7[64];
			PointAffine Mpublickey[1];
			unsigned char chaincode[CANARY_LENGTH];
			unsigned char out[32 + CANARY_LENGTH];
			unsigned char j;

			printf("\n\n *********************************************************************************************** ");
			jaz0 = "";
			if (seed == "en") {
				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();
				
				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
			}

			if (seed == "es") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			if (seed == "ja") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			if (seed == "it") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			if (seed == "fr") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			if (seed == "ko") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			if (seed == "zh_Hans") {


				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
			}
			if (seed == "zh_Hant") {

				if (zez == "3") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "6") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "9") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "12") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "15") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "18") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "21") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}
				if (zez == "24") {
					auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

					std::stringstream ssp;
					ssp << vhod;
					jaz0 += ssp.str();

				}

			}
			
			//string nos0 = "circle bulb patrol security sniff fire engage ankle vehicle miss whip story";

			string salt = "mnemonic";

			unsigned char hseed0[64];
			pbkdf2_hmac_sha512(hseed0, 64, (const uint8_t*)jaz0.c_str(), jaz0.length(),
				(const uint8_t*)salt.c_str(), salt.length(),
				2048);

			string hhexx0 = sha512_hex(hseed0);

			printf("\n Words(%s): %s \n SEED    : %s \n", zez.c_str(), jaz0.c_str(), hhexx0.c_str());


			bip32SeedToNode(master_node, hseed0, 64);
			getMasterPublicKey(Mpublickey, chaincode, master_node);
			printf("\n Mpublic x          : ");
			bigPrintVariableSize(Mpublickey->x, 32, true);

			printf("\n Mpublic y          : ");
			bigPrintVariableSize(Mpublickey->y, 32, true);

			printf("\n Mpublic point      : %x ", Mpublickey->is_point_at_infinity);
			printf("\n Chaincode          : ");
			bigPrintVariableSize(chaincode, 32, true);
			printf("\n ================================================================================================ ");
			printf("\n BIP38 Root mnemonic");
			startKey.SetInt32(0);
			sha256(hseed0, 64, (unsigned char*)startKey.bits64);

			printf("\n Private key: %s ", startKey.GetBase16().c_str());

			bool compressed = (searchMode == SEARCH_COMPRESSED);
			Point p = secp->ComputePublicKey(&startKey);
			printf("\n Private hex: %s ", secp->GetPrivAddress(compressed, startKey).c_str());
			printf("\n Public key : %s ", secp->GetPublicKeyHex(compressed, p).c_str());
			bool isComp;
			printf("\n Address    : %s ", secp->GetAddress(P2PKH, isComp, p).c_str());
			printf("\n ================================================================================================ ");


			printf("\n BIP32 ");
			printf("\n Account 0 m/0/0 -> m/0/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 2);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: m/0/%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}
			printf("\n BIP32 ");
			printf("\n Account 1 m/1/0 -> m/1/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 1,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 2);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: m/1/%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}
			printf("\n BIP44 ");
			printf("\n Account 0 External 0 m/44'/0'/0'/0/0 -> m/44'/0'/0'/0/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 5);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: 0x8000002C,0x80000000,0x80000000,0,%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}

			printf("\n BIP44 ");
			printf("\n Account 0 External 1 m/44'/0'/0'/1/0 -> m/44'/0'/0'/1/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 5);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: 0x8000002C,0x80000000,0x80000000,1,%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}
			printf("\n BIP44 ");
			printf("\n Account 1 External 0 m/44'/0'/1'/0/0 -> m/44'/0'/1'/0/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 5);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: 0x8000002C,0x80000000,0x80000001,0,%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}
			printf("\n BIP44 ");
			printf("\n Account 1 External 1 m/44'/0'/1'/1/0 -> m/44'/0'/1'/1/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 5);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: 0x8000002C,0x80000000,0x80000001,1,%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}

			printf("\n BIP44 Ethereum");
			printf("\n Account 0 External 0 m/44'/60'/0'/0/0 -> m/44'/60'/0'/0/%d", nbit);
			for (int nk1 = 0; nk1 < nbit; nk1++) {

				unsigned long TxPath[20] = { 0x8000002C,0x8000003C,0x80000000,0,nk1 };
				bip32DerivePrivate(out, master_node, TxPath, 5);

				unsigned int size = 32;
				unsigned int ik;
				nos2 = "";
				for (ik = (uint8_t)(size - 1); ik < size; ik--)
				{
					char s[32];
					snprintf(s, 32, "%02X", out[ik]);
					string str777(s);
					nos2 = nos2 + str777;
				}

				char* cstr959 = &nos2[0];
				key.SetBase16(cstr959);

				printf("\n Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,%d Private key: %s", nk1, key.GetBase16().c_str());

				Int km(&key);
				km.Add((uint64_t)CPU_GRP_SIZE / 1024);
				startP = secp->ComputePublicKey(&km);

				if (ph->rekeyRequest) {
					getCPUStartingKey(thId, key, startP);
					ph->rekeyRequest = false;
				}

				int i = 0;
				dx[i].ModSub(&Gn[i].x, &startP.x);
				dx[i + 1].ModSub(&_2Gn.x, &startP.x);
				grp->ModInv();

				pts[1] = startP;
				pn = startP;
				dyn.Set(&Gn[i].y);
				dyn.ModNeg();
				dyn.ModSub(&pn.y);
				_s.ModMulK1(&dyn, &dx[i]);
				_p.ModSquareK1(&_s);
				pn.x.ModNeg();
				pn.x.ModAdd(&_p);
				pn.x.ModSub(&Gn[i].x);
				pn.y.ModSub(&Gn[i].x, &pn.x);
				pn.y.ModMulK1(&_s);
				pn.y.ModAdd(&Gn[i].y);
				pts[0] = pn;

				switch (searchMode) {
				case SEARCH_COMPRESSED:
					checkAddresses(true, key, i, pts[i]);
					break;
				case SEARCH_UNCOMPRESSED:
					checkAddresses(false, key, i, pts[i]);
					break;
				case SEARCH_BOTH:
					checkAddresses(true, key, i, pts[i]);
					checkAddresses(false, key, i, pts[i]);
					break;
				}
				counters[thId] += 1;

			}
			printf("\n\n");
			//ph->isRunning = false;

		}

	}

	if (rekey == 1) {

    
		int thId = ph->threadId;
		counters[thId] = 0;

		IntGroup* grp = new IntGroup(CPU_GRP_SIZE / 1024 + 1);

		Int  key;
		Point startP;
		getCPUStartingKey(thId, key, startP);

		Int dx[CPU_GRP_SIZE / 1024 + 1];
		Point pts[CPU_GRP_SIZE];

		Int dy;
		Int dyn;
		Int _s;
		Int _p;
		Point pp;
		Point pn;
		grp->Set(dx);

		ph->hasStarted = true;
		ph->rekeyRequest = false;

		if (thId == 0) {
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;

				jaz0 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
						
					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz0 += ssp.str();
					}
				}

				string salt = "mnemonic";

				unsigned char hseed0[64];
				pbkdf2_hmac_sha512(hseed0, 64, (const uint8_t*)jaz0.c_str(), jaz0.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode(master_node, hseed0, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos0 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos0 = nos0 + str777;
					}

					char* cstr959 = &nos0[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}
			}
		}
		if (thId == 1) {
			
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;
				
				jaz1 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz1 += ssp.str();

					}

				}

				string salt = "mnemonic";

				unsigned char hseed2[64];
				pbkdf2_hmac_sha512(hseed2, 64, (const uint8_t*)jaz1.c_str(), jaz1.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode2(master_node, hseed2, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate2(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos1 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos1 = nos1 + str777;
					}

					char* cstr959 = &nos1[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
			}
		}
		if (thId == 2) {
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;

				jaz2 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz2 += ssp.str();

					}

				}

				string salt = "mnemonic";

				unsigned char hseed3[64];
				pbkdf2_hmac_sha512(hseed3, 64, (const uint8_t*)jaz2.c_str(), jaz2.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode3(master_node, hseed3, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate3(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos2 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos2 = nos2 + str777;
					}

					char* cstr959 = &nos2[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
			}

		}
		if (thId == 3) {
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;

				jaz3 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}

				}

				string salt = "mnemonic";

				unsigned char hseed4[64];
				pbkdf2_hmac_sha512(hseed4, 64, (const uint8_t*)jaz3.c_str(), jaz3.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode4(master_node, hseed4, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate4(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos3 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos3 = nos3 + str777;
					}

					char* cstr959 = &nos3[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;

				}
			}

		}
		if (thId == 4) {
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;

				jaz4 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz3 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz4 += ssp.str();

					}
				}

				string salt = "mnemonic";

				unsigned char hseed5[64];
				pbkdf2_hmac_sha512(hseed5, 64, (const uint8_t*)jaz4.c_str(), jaz4.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode4(master_node, hseed5, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos4 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos4 = nos4 + str777;
					}

					char* cstr959 = &nos4[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
			}
		}
		if (thId == 5) {
			while (1 < 2) {
				akk += 1;
				uint8_t seed7[64];
				PointAffine Mpublickey[1];
				unsigned char chaincode[CANARY_LENGTH];
				unsigned char out[32 + CANARY_LENGTH];
				unsigned char j;

				jaz5 = "";
				if (seed == "en") {
					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::en);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "es") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::es);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "ja") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ja);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "it") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::it);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "fr") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::fr);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "ko") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::ko);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();
					}
				}
				if (seed == "zh_Hans") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hans);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
				}
				if (seed == "zh_Hant") {

					if (zez == "3") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_32, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "6") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_64, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "9") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_96, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "12") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_128, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "15") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_160, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "18") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_192, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "21") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_224, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
					if (zez == "24") {
						auto vhod = BIP39::generate_mnemonic(BIP39::entropy_bits_t::_256, BIP39::language::zh_Hant);

						std::stringstream ssp;
						ssp << vhod;
						jaz5 += ssp.str();

					}
				}

				string salt = "mnemonic";

				unsigned char hseed6[64];
				pbkdf2_hmac_sha512(hseed6, 64, (const uint8_t*)jaz5.c_str(), jaz5.length(),
					(const uint8_t*)salt.c_str(), salt.length(),
					2048);

				bip32SeedToNode4(master_node, hseed6, 64);

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0,nk1 };
					bip32DerivePrivate6(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 1,nk1 };
					bip32DerivePrivate5(out, master_node, TxPath, 2);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,0,nk1 };
					bip32DerivePrivate6(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);


					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000000,1,nk1 };
					bip32DerivePrivate6(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000001,0x80000000,0,nk1 };
					bip32DerivePrivate6(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}

				for (int nk1 = 0; nk1 < nbit; nk1++) {

					unsigned long TxPath[20] = { 0x8000002C,0x80000000,0x80000001,1,nk1 };
					bip32DerivePrivate6(out, master_node, TxPath, 5);

					unsigned int size = 32;
					unsigned int ik;
					nos5 = "";
					for (ik = (uint8_t)(size - 1); ik < size; ik--)
					{
						char s[32];
						snprintf(s, 32, "%02X", out[ik]);
						string str777(s);
						nos5 = nos5 + str777;
					}

					char* cstr959 = &nos5[0];
					key.SetBase16(cstr959);

					Int km(&key);
					km.Add((uint64_t)CPU_GRP_SIZE / 1024);
					startP = secp->ComputePublicKey(&km);

					if (ph->rekeyRequest) {
						getCPUStartingKey(thId, key, startP);
						ph->rekeyRequest = false;
					}

					int i = 0;
					dx[i].ModSub(&Gn[i].x, &startP.x);
					dx[i + 1].ModSub(&_2Gn.x, &startP.x);
					grp->ModInv();

					pts[1] = startP;
					pn = startP;
					dyn.Set(&Gn[i].y);
					dyn.ModNeg();
					dyn.ModSub(&pn.y);
					_s.ModMulK1(&dyn, &dx[i]);
					_p.ModSquareK1(&_s);
					pn.x.ModNeg();
					pn.x.ModAdd(&_p);
					pn.x.ModSub(&Gn[i].x);
					pn.y.ModSub(&Gn[i].x, &pn.x);
					pn.y.ModMulK1(&_s);
					pn.y.ModAdd(&Gn[i].y);
					pts[0] = pn;

					switch (searchMode) {
					case SEARCH_COMPRESSED:
						checkAddresses(true, key, i, pts[i]);
						break;
					case SEARCH_UNCOMPRESSED:
						checkAddresses(false, key, i, pts[i]);
						break;
					case SEARCH_BOTH:
						checkAddresses(true, key, i, pts[i]);
						checkAddresses(false, key, i, pts[i]);
						break;
					}
					counters[thId] += 1;
				}
			}
		}
	}
}

// ----------------------------------------------------------------------------

void LostCoins::getGPUStartingKeys(int thId, int groupSize, int nbThread, Int *keys, Point *p)
{
   
	for (int i = 0; i < nbThread; i++) {
		
		exit(-1);
	
	}
		

}

void LostCoins::FindKeyGPU(TH_PARAM* ph)
{

	bool ok = true;

#ifdef WITHGPU

	// Global init
	int thId = ph->threadId;
	Int tRangeStart = ph->rangeStart1;
	Int tRangeEnd = ph->rangeEnd1;
	GPUEngine g(ph->gridSizeX, ph->gridSizeY, ph->gpuId, maxFound, (rekey != 0),
		BLOOM_N, bloom->get_bits(), bloom->get_hashes(), bloom->get_bf(), DATA, TOTAL_ADDR);
	int nbThread = g.GetNbThread();
	Point* p = new Point[nbThread];
	Int* keys = new Int[nbThread];
	vector<ITEM> found;
	printf("  GPU         : %s\n\n", g.deviceName.c_str());
	counters[thId] = 0;

	getGPUStartingKeys(thId, g.GetGroupSize(), nbThread, keys, p);
	g.SetSearchMode(searchMode);
	g.SetSearchType(searchType);

	getGPUStartingKeys(thId, g.GetGroupSize(), nbThread, keys, p);
	ok = g.SetKeys(p);
	ph->rekeyRequest = false;

	ph->hasStarted = true;

	// GPU Thread
	while (ok && !endOfSearch) {

		if (ph->rekeyRequest) {
			getGPUStartingKeys(thId, g.GetGroupSize(), nbThread, keys, p);
			ok = g.SetKeys(p);
			ph->rekeyRequest = false;
		}

		// Call kernel
		ok = g.Launch(found, false);

		for (int i = 0; i < (int)found.size() && !endOfSearch; i++) {

			ITEM it = found[i];
			//checkAddr(it.hash, keys[it.thId], it.incr, it.endo, it.mode);
			string addr = secp->GetAddress(searchType, it.mode, it.hash);
			if (checkPrivKey(addr, keys[it.thId], it.incr, it.endo, it.mode)) {
				nbFoundKey++;
			}

		}

		if (ok) {
			for (int i = 0; i < nbThread; i++) {
				keys[i].Add((uint64_t)STEP_SIZE);
			}
			counters[thId] += STEP_SIZE * nbThread; // Point +  endo1 + endo2 + symetrics
		}
		//ok = g.ClearOutBuffer();
	}
	delete[] keys;
	delete[] p;

#else
	ph->hasStarted = true;
	printf("GPU code not compiled, use -DWITHGPU when compiling.\n");
#endif

	ph->isRunning = false;

}

// ----------------------------------------------------------------------------

bool LostCoins::isAlive(TH_PARAM *p)
{

	bool isAlive = true;
	int total = nbCPUThread + nbGPUThread;
	for (int i = 0; i < total; i++)
		isAlive = isAlive && p[i].isRunning;

	return isAlive;

}

// ----------------------------------------------------------------------------

bool LostCoins::hasStarted(TH_PARAM *p)
{

	bool hasStarted = true;
	int total = nbCPUThread + nbGPUThread;
	for (int i = 0; i < total; i++)
		hasStarted = hasStarted && p[i].hasStarted;

	return hasStarted;

}

// ----------------------------------------------------------------------------

void LostCoins::rekeyRequest(TH_PARAM *p)
{

	bool hasStarted = true;
	int total = nbCPUThread + nbGPUThread;
	for (int i = 0; i < total; i++)
		p[i].rekeyRequest = true;

}


// ----------------------------------------------------------------------------

uint64_t LostCoins::getGPUCount()
{
	uint64_t count = 0;
	for (int i = 0; i < nbGPUThread; i++)
		count += counters[0x80L + i];
	return count;

}

uint64_t LostCoins::getCPUCount()
{

	uint64_t count = 0;
	for (int i = 0; i < nbCPUThread; i++)
		count += counters[i];
	return count;

}

// ----------------------------------------------------------------------------

void LostCoins::Search(int nbThread, std::vector<int> gpuId, std::vector<int> gridSize, bool& should_exit)
{
	
	double t0;
	double t1;
	endOfSearch = false;
	nbCPUThread = nbThread;
	nbGPUThread = (useGpu ? (int)gpuId.size() : 0);
	nbFoundKey = 0;
	memset(counters, 0, sizeof(counters));

	//printf("Number of CPU thread: %d\n\n", nbCPUThread);

	TH_PARAM *params = (TH_PARAM *)malloc((nbCPUThread + nbGPUThread) * sizeof(TH_PARAM));
	memset(params, 0, (nbCPUThread + nbGPUThread) * sizeof(TH_PARAM));

	// Launch CPU threads
	for (int i = 0; i < nbCPUThread; i++) {
		params[i].obj = this;
		params[i].threadId = i;
		params[i].isRunning = true;

#ifdef WIN64
		DWORD thread_id;
		CreateThread(NULL, 0, _FindKey, (void *)(params + i), 0, &thread_id);
		ghMutex = CreateMutex(NULL, FALSE, NULL);
#else
		pthread_t thread_id;
		pthread_create(&thread_id, NULL, &_FindKey, (void *)(params + i));
		ghMutex = PTHREAD_MUTEX_INITIALIZER;
#endif
	}

	// Launch GPU threads
	for (int i = 0; i < nbGPUThread; i++) {
		params[nbCPUThread + i].obj = this;
		params[nbCPUThread + i].threadId = 0x80L + i;
		params[nbCPUThread + i].isRunning = true;
		params[nbCPUThread + i].gpuId = gpuId[i];
		params[nbCPUThread + i].gridSizeX = gridSize[2 * i];
		params[nbCPUThread + i].gridSizeY = gridSize[2 * i + 1];

#ifdef WIN64
		DWORD thread_id;
		CreateThread(NULL, 0, _FindKeyGPU, (void *)(params + (nbCPUThread + i)), 0, &thread_id);
#else
		pthread_t thread_id;
		pthread_create(&thread_id, NULL, &_FindKeyGPU, (void *)(params + (nbCPUThread + i)));
#endif
	}

#ifndef WIN64
	setvbuf(stdout, NULL, _IONBF, 0);
#endif

	uint64_t lastCount = 0;
	uint64_t gpuCount = 0;
	uint64_t lastGPUCount = 0;

	// Key rate smoothing filter
#define FILTER_SIZE 8
	double lastkeyRate[FILTER_SIZE];
	double lastGpukeyRate[FILTER_SIZE];
	uint32_t filterPos = 0;

	double keyRate = 0.0;
	double gpuKeyRate = 0.0;
	char timeStr[256];

	memset(lastkeyRate, 0, sizeof(lastkeyRate));
	memset(lastGpukeyRate, 0, sizeof(lastkeyRate));

	// Wait that all threads have started
	while (!hasStarted(params)) {
		Timer::SleepMillis(500);
	}

	// Reset timer
	Timer::Init();
	t0 = Timer::get_tick();
	startTime = t0;
	Int p100;
	Int ICount;
	p100.SetInt32(100);
	int completedPerc = 0;
	uint64_t rKeyCount = 0;
	while (isAlive(params)) {

		int delay = 1000;
		while (isAlive(params) && delay > 0) {
			Timer::SleepMillis(500);
			delay -= 500;
		}

		gpuCount = getGPUCount();
		uint64_t count = getCPUCount() + gpuCount;
		ICount.SetInt64(count);
		int completedBits = ICount.GetBitLength();

		

		t1 = Timer::get_tick();
		keyRate = (double)(count - lastCount) / (t1 - t0);
		gpuKeyRate = (double)(gpuCount - lastGPUCount) / (t1 - t0);
		lastkeyRate[filterPos % FILTER_SIZE] = keyRate;
		lastGpukeyRate[filterPos % FILTER_SIZE] = gpuKeyRate;
		filterPos++;

		double avgKeyRate = 0.0;
		double avgGpuKeyRate = 0.0;
		uint32_t nbSample;
		for (nbSample = 0; (nbSample < FILTER_SIZE) && (nbSample < filterPos); nbSample++) {
			avgKeyRate += lastkeyRate[nbSample];
			avgGpuKeyRate += lastGpukeyRate[nbSample];
		}
		avgKeyRate /= (double)(nbSample);
		avgGpuKeyRate /= (double)(nbSample);


		
		if (diz == 0) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r                                                    [%s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					avgKeyRate / 1000000.0,
					avgGpuKeyRate / 1000000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}
		}
		if (diz == 1) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [Mnemonic: %d] [Addresses: %s] [Speed: %.0f/s] [F: %d] [%s]        ",
					toTimeStr(t1, timeStr),
					akk,
					formatThousands(count).c_str(),
					avgKeyRate,
					nbFoundKey,
					jaz0.c_str());
			}
		}
		if (diz == 2) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					avgKeyRate / 1000000.0,
					avgGpuKeyRate / 1000000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}
		}
		if (diz == 3) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [CPU: %.2f Kk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					avgKeyRate / 1000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}

		}
		if (diz == 4) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [%064s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [C: %d%%] [T: %s (%d bit)] [F: %d]              ",
					toTimeStr(t1, timeStr),
					rangeDiff3.GetBase16().c_str(),
					avgKeyRate / 1000000.0,
					avgGpuKeyRate / 1000000.0,
					completedPerc,
					formatThousands(count).c_str(),
					completedBits,
					nbFoundKey);
			}

		}
		if (diz == 5) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r                                    [%s] [CPU: %.2f Kk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					avgKeyRate / 1000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}

		}
		if (diz == 6) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [%064s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					rangeDiff3.GetBase16().c_str(),
					avgKeyRate / 1000000.0,
					avgGpuKeyRate / 1000000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}
		}

		if (diz > 6) {
			if (isAlive(params)) {
				memset(timeStr, '\0', 256);
				printf("\r  [%s] [CPU+GPU: %.2f Mk/s] [GPU: %.2f Mk/s] [T: %s] [F: %d]  ",
					toTimeStr(t1, timeStr),
					avgKeyRate / 1000000.0,
					avgGpuKeyRate / 1000000.0,
					formatThousands(count).c_str(),
					nbFoundKey);
			}
		}
		
		if (rekey == 0) {

			if ((count - lastRekey) > (1 * 1)) {
				// Rekey request
				rekeyRequest(params);
				lastRekey = count;
			}
			
		}
		if (rekey == 1) {

			if ((count - lastRekey) > (1 * 100)) {
				// Rekey request
				rekeyRequest(params);
				lastRekey = count;
			}

		}
		
		if (rekey == 2) {

			if (nbit2 > 0) {

				if ((count - lastRekey) > (1 * 1)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
			else {

				if ((count - lastRekey) > (1000000000 * maxFound)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
		}
		if (rekey == 3) {

			if (nbit2 > 0) {

				if ((count - lastRekey) > (1 * 1)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
			else {

				if ((count - lastRekey) > (47200000 * maxFound)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
		}
		if (rekey == 4) {

			if (nbit2 > 0) {

				if ((count - lastRekey) > (1 * 1)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
			else {

				if ((count - lastRekey) > (1000000000 * maxFound)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
		}

		if (rekey == 5) {

			if (nbit2 > 0) {

				if ((count - lastRekey) > (1 * 1)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
			else {

				if ((count - lastRekey) > (1000000000)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
		}
		
		if (rekey == 6) {

			if (nbit2 > 0) {

				if ((count - lastRekey) > (1 * 1)) {
					// Rekey request
					rekeyRequest(params);
					lastRekey = count;
				}
			}
			else {

				if ((count - lastRekey) > (1000000000 * maxFound)) {
					rekeyRequest(params);
					lastRekey = count;
				}
			}
		}

		if (rekey > 6) {
			if ((count - lastRekey) > (1 * 1)) {
				rekeyRequest(params);
				lastRekey = count;
			}
		}

		lastCount = count;
		lastGPUCount = gpuCount;
		t0 = t1;
		//endOfSearch = should_exit;


		if (rekey == 1) {
			lastCount = count;
			lastGPUCount = gpuCount;
			t0 = t1;
			if (should_exit || completedPerc > 101)
				endOfSearch = true;
		}

		
	}
	
	free(params);

}

string LostCoins::GetHex(vector<unsigned char> &buffer)
{
	string ret;

	char tmp[128];
	for (int i = 0; i < (int)buffer.size(); i++) {
		sprintf(tmp, "%02X", buffer[i]);
		ret.append(tmp);
	}
	return ret;
}

int LostCoins::CheckBloomBinary(const uint8_t *hash)
{
	if (bloom->check(hash, 20) > 0) {
		uint8_t* temp_read;
		uint64_t half, min2, max, current;
		int64_t rcmp;
		int32_t r = 0;
		min2 = 0;
		current = 0;
		max = TOTAL_ADDR;
		half = TOTAL_ADDR;
		while (!r && half >= 1) {
			half = (max - min2) / 2;
			temp_read = DATA + ((current + half) * 20);
			rcmp = memcmp(hash, temp_read, 20);
			if (rcmp == 0) {
				r = 1;  //Found!!
			}
			else {
				if (rcmp < 0) { //data < temp_read
					max = (max - half);
				}
				else { // data > temp_read
					min2 = (min2 + half);
				}
				current = min2;
			}
		}
		return r;
	}
	return 0;
}

std::string LostCoins::formatThousands(uint64_t x)
{
	char buf[32] = "";

	sprintf(buf, "%llu", x);

	std::string s(buf);

	int len = (int)s.length();

	int numCommas = (len - 1) / 3;

	if (numCommas == 0) {
		return s;
	}

	std::string result = "";

	int count = ((len % 3) == 0) ? 0 : (3 - (len % 3));

	for (int i = 0; i < len; i++) {
		result += s[i];

		if (count++ == 2 && i < len - 1) {
			result += ",";
			count = 0;
		}
	}
	return result;
}

char* LostCoins::toTimeStr(int sec, char* timeStr)
{
	int h, m, s;
	h = (sec / 3600);
	m = (sec - (3600 * h)) / 60;
	s = (sec - (3600 * h) - (m * 60));
	sprintf(timeStr, "%0*d:%0*d:%0*d", 2, h, 2, m, 2, s);
	return (char*)timeStr;
}

namespace BIP39 {

	using random_bytes_engine = std::independent_bits_engine<
		std::default_random_engine, 16, uint16_t>;

	const char* const* get_string_table(language lang) {
		switch (lang) {
		case language::en: return english_table;
		case language::es: return spanish_table;
		case language::ja: return japanese_table;
		case language::it: return italian_table;
		case language::fr: return french_table;
		case language::ko: return korean_table;
		case language::zh_Hans: return chinese_simplified_table;
		case language::zh_Hant: return chinese_traditional_table;

		default:
			assert("error unsupported language");
			return nullptr;
		};
	}

	namespace {

		uint8_t bip39_shift(size_t bit)
		{
			return (1 << (BYTE_BITS - (bit % BYTE_BITS) - 1));
		}
		

		int get_word_index(const char* const* const lexicon, const std::string& word) {
			for (auto i = 0u; i < NUM_BIP39_WORDS; ++i) {
				char w[MAX_BIP39_WORD_OCTETS] = {};
				strcpy_P(w, (char*)pgm_read_ptr_far(&(lexicon[i]))); // NOLINT
				if (strcmp(w, word.c_str()) == 0) {
					return i;
				}
			}
			return -1;
		}

		void append_checksum_bits(std::vector<uint8_t>& entropyBuffer) {
			const auto ENT = entropyBuffer.size() * BYTE_BITS;
			const auto CS = ENT / 32u;

			picosha2::hash256_one_by_one hasher;
			hasher.process(entropyBuffer.begin(), entropyBuffer.end());
			hasher.finish();
			std::vector<uint8_t> hash(picosha2::k_digest_size);
			hasher.get_hash_bytes(hash.begin(), hash.end());
			const auto checksum_byte_count = min((CS / BYTE_BITS) + 1, picosha2::k_digest_size);
			for (auto i = 0u; i < checksum_byte_count; ++i) {
				entropyBuffer.push_back(hash[i]);
			}
		}

	}

	word_list create_mnemonic(std::vector<uint8_t>& entropy, language lang /* = language::en */) {
		const size_t entropy_bits = (entropy.size() * BYTE_BITS);
		const size_t check_bits = (entropy_bits / ENTROPY_BIT_DIVISOR);
		const size_t total_bits = (entropy_bits + check_bits);
		const size_t word_count = (total_bits / BITS_PER_WORD);

		append_checksum_bits(entropy);
		size_t bit = 0;
		const auto lexicon = get_string_table(lang);
		word_list words;
		
		for (size_t i = 0; i < word_count; i++)
		{
			size_t position = 0;
			for (size_t loop = 0; loop < BITS_PER_WORD; loop++)
			{
				bit = (i * BITS_PER_WORD + loop);
				position <<= 1;

				const auto byte = bit / BYTE_BITS;
				if ((entropy[byte] & bip39_shift(bit)) > 0)
				{
					position++;
				}
				
			}

			assert(position < DICTIONARY_SIZE);
			char word[MAX_BIP39_WORD_OCTETS] = {};
			strcpy_P(word, (char*)pgm_read_ptr_far(&(lexicon[position]))); // NOLINT
			words.add(word);
		}
		return words;
	}

	word_list generate_mnemonic(entropy_bits_t entropy /* = entropy_bits::_128 */, language lang /* = language::en */) {
		const auto entropy_bits = static_cast<entropy_bits_int_type>(entropy);
		assert(entropy_bits % (MNEMONIC_SEED_MULTIPLE * BYTE_BITS) == 0);

		const auto check_bits = (entropy_bits / ENTROPY_BIT_DIVISOR);
		const auto total_bits = (entropy_bits + check_bits);
		const auto word_count = (total_bits / BITS_PER_WORD);

		assert((total_bits % BITS_PER_WORD) == 0);
		assert((word_count % MNEMONIC_WORD_MULTIPLE) == 0);

		random_bytes_engine rbe;
		rbe.seed(std::random_device()());
		std::vector<uint8_t> data(entropy_bits / BYTE_BITS);
		std::generate(begin(data), end(data), [&rbe]() { return static_cast<uint8_t>(std::ref(rbe)()); });
		return create_mnemonic(data, lang);
	}

	std::vector<uint8_t> decode_mnemonic(const word_list& mnemonic, const std::string& password /* = "" */) {
		return std::vector<uint8_t>();
	}

	bool valid_mnemonic(const word_list& mnemonic, language lang /* = language::en */) {
		const auto word_count = mnemonic.size();
		if ((word_count % MNEMONIC_WORD_MULTIPLE) != 0) {
			return false;
		}

		const auto total_bits = BITS_PER_WORD * word_count;
		const auto check_bits = total_bits / (ENTROPY_BIT_DIVISOR + 1);
		const auto entropy_bits = total_bits - check_bits;

		assert((entropy_bits % BYTE_BITS) == 0);

		size_t bit = 0;
		std::vector<uint8_t> data((total_bits + BYTE_BITS - 1) / BYTE_BITS, 0);
		const auto lexicon = get_string_table(lang);

		for (const auto& word : mnemonic)
		{
			const auto position = get_word_index(lexicon, word);
			if (position == -1) { return false; }

			for (size_t loop = 0; loop < BITS_PER_WORD; loop++, bit++)
			{
				if ((position & (1 << (BITS_PER_WORD - loop - 1))) != 0)
				{
					const auto byte = bit / BYTE_BITS;
					data[byte] |= bip39_shift(bit);
				}
			}
		}

		data.resize(entropy_bits / BYTE_BITS);
		const auto new_mnemonic = create_mnemonic(data, lang);
		return std::equal(new_mnemonic.begin(), new_mnemonic.end(), mnemonic.begin());
	}

}
