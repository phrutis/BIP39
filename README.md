# BIP39
Experimental project BIP39/Bip32/Bip44. This is a modified version [LostCoins](https://github.com/phrutis/LostCoins)
## Quick start
- Сonvert addresses 1... into binary hashes RIPEMD160 use [b58dec](https://github.com/phrutis/LostCoins/blob/main/Others/b58dec.exe) command: ```b58dec.exe addresses.txt base160.bin```
- It is important to sort the base160.bin file otherwise the Bloom search filter will not work as expected.
- To sort base160.bin use the program [RMD160-Sort](https://github.com/phrutis/LostCoins/blob/main/Others/RMD160-Sort.exe) command: ```RMD160-Sort.exe base160.bin hex160-Sort.bin``` 
## Mode 0 (test mode)
## An illustrative example of work  
 - For TEST ```BIP39.exe -t 1 -r 0 -f test.bin``` (Default: language en, 12 words, 10 addresses)
```
C:\Users\user>BIP39.exe -t 1 -r 0 -f test.bin

 BIP39 v1.0 (17.10.2021)

 SEARCH MODE  : COMPRESSED
 DEVICE       : CPU
 CPU THREAD   : 1
 GPU IDS      : 0
 GPU GRIDSIZE : -1x128
 HASH160 FILE : test.bin
 OUTPUT FILE  : Found.txt

 Loading      : 100 %
 Loaded       : 75,471 address

Bloom at 0000022F0737BA30
  Version     : 2.1
  Entries     : 150942
  Error       : 0.0000010000
  Bits        : 4340363
  Bits/Elem   : 28.755175
  Bytes       : 542546 (0 MB)
  Hash funcs  : 20

  Start Time  : Sun Oct 17 23:49:11 2021

  TEST Mode   : 0
  Mode BIP    : BIP39 -> Bip32 -> Bip44
  Language    : en
  Use words   : 12
  Check       : 10 addresses for each account
  Site        : https://github.com/phrutis/BIP39
  Donate      : bc1qh2mvnf5fujg93mwl8pe688yucaw9sflmwsukz9



 ***********************************************************************************************
 Words(12): hair bleak describe shoot enlist tuition extra pyramid sun scout wheat square
 SEED    : cab2b879c523cf077f56b1ecb52a2e0b7188708b5be019c1062f93e0fd81fdafb9b439fdfdb355068534fc70cb4d9a0b9aa4ae03bfaa81b7394c1051a9adf86f

 Mpublic x          : b2b6628873d3073bfefe7d9edc78bd42cb46373151ed71d1cee84c5695ec02e4
 Mpublic y          : a34ce6ea26cb6f733341758e5d25d325d45525a9522f4f2f6d8e428d26936032
 Mpublic point      : 0
 Chaincode          : 7d6869393337deddde46643ff4a551992b3d9a82caacb9272ac89eec8579f206
 ================================================================================================
 BIP38 Root mnemonic
 Private key: B3B0B25A44894381DBA67B5F346F706C1857E4D404F7AEC08BE80DA6952A7E0F
 Private hex: L3F1FiTW5Pb29EeyMRJzmMZkpYxavW7dT4FGSUc6VtafXyARiozj
 Public key : 0302A2A0C4EE9224BFCE6E00A0FD8734EACF07504BF0535C816E034484D8C45AEB
 Address    : 1JK42gNVLe4sVojCsJRv7qsUBVfXsXniF3
 ================================================================================================
 BIP32
 Account 0 m/0/0 -> m/0/10
 Derivation Path: m/0/0 Private key: 6F2AD9CA17F10F2D56389D208731812158ED5158DDC5EC77BBC5291A366C66B1
 Derivation Path: m/0/1 Private key: BFF5144BDBADAF8A31B7F22E9C8DC3BAE48552A75A5E98F276BD886EBEF9B2C9
 Derivation Path: m/0/2 Private key: A316409EE48538D3D2A790E80DE096398047D25CF72535CCE02512CB54D09434
 Derivation Path: m/0/3 Private key: 76B42844F187FFFF7EA1754A79FC3CE867E4F2530E694BD97F81584014E7259F
 Derivation Path: m/0/4 Private key: BE552C46034A22FF932CB23FE755DB9F2672B9DC5A1F761E2347619204ED5933
 Derivation Path: m/0/5 Private key: 7384D669F75D629E7725B82669E3CD67E10C040A3D783D4DD185DB3D8347E510
 Derivation Path: m/0/6 Private key: E04E1C1B26ABF72893BC8B8D158135D312F9BC0B6D5F0E05C64330EFDD23BA7
 Derivation Path: m/0/7 Private key: CE28BFE656B412E29856CD637A2E2ED17BA1ED9631FDAACCC9917F0F0F185009
 Derivation Path: m/0/8 Private key: BD6E53110F5D5140B4139668D7004A5FBE6008867A7CDEE3F0F4C57392DA24CF
 Derivation Path: m/0/9 Private key: 7D33C9511012FFA8367B70F369977223B61BE19546412FF18F40D24DAEE351A1
 BIP32
 Account 1 m/1/0 -> m/1/10
 Derivation Path: m/1/0 Private key: 680CEF4E3BC6F4A4362CA7EE2FECDFC73B7318C87C28056F452B01FEC062A48C
 Derivation Path: m/1/1 Private key: E6B292D5E4D37FD93E98F77583BFC456B461B92C3AB46E62FF2843A01281AC10
 Derivation Path: m/1/2 Private key: 71FB19690541ECA0F0D70B41C6981AA339A25C67AC48E61147BE3EBFB6F62580
 Derivation Path: m/1/3 Private key: FFABABFF39B4633B34D920946A9920279B8077272329FD6C856837474B38A076
 Derivation Path: m/1/4 Private key: 156DA15BF802F1E4AE40CBBD0D2E5A40986D7261B563F37BEC927F55F9171D79
 Derivation Path: m/1/5 Private key: 10A0D77A46BF2EC0180F1896FC39DA76490DCA3DECDCB1E0730C9A5BD0C78821
 Derivation Path: m/1/6 Private key: AE3686DF889A7776A9DEF70B233361D638BE32A5C21750E2BEDE12E4F6757E17
 Derivation Path: m/1/7 Private key: EFE6DEAAEC97751F66481367AA91BE45DF6F53307CC0CABC4DEA6F91EEA6CCD2
 Derivation Path: m/1/8 Private key: 86C22DBAFBA3440C49BBC0005B00D5A78C68C0D36F167018CC3A0B589851233
 Derivation Path: m/1/9 Private key: 3BF6450CF34762D4764C99AEF53E46A579482373A4FDD95632D526D335E1D145
 BIP44
 Account 0 External 0 m/44'/0'/0'/0/0 -> m/44'/0'/0'/0/10
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,0 Private key: E614966DED0A22EE35C26143A0B3A837A4CB65293FA35962650958AC0421CF98
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,1 Private key: 9AEDFFDEA847F5420B8FBAE0E7B203520162D843970AB680791413C2D33A27E5
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,2 Private key: 7E9C275F3FDE67E092D8AD3E15C11C759EEF49A7CAD028F6FA5609D1AB50DCAC
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,3 Private key: EE25942A4858694E5249B188AB21B9F3D48FC58C438969548A900D942F5249E5
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,4 Private key: 4193A8CB5C31E020D7CAB25C62CB1A1BE83C570D179AFA22254681E380074C77
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,5 Private key: 9BDD01E63C2F445CF6DD5AADF1921BAB45DF7852C2DF9BB46C4E5E8FD7F0FC4B
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,6 Private key: 2ADF225AE1BFAC0F3B577363302A94AA4852D7FA85EB721E9246A7E2670814A5
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,7 Private key: 4944AD37BB8D94AB130CDE3F7EA022B1714271FB92FDAE9506A7E773BD0042CE
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,8 Private key: 7BC857749030F44CBF4B12B110F49A03770F6CEA709FE568A0D93892A9D28DBE
 Derivation Path: 0x8000002C,0x80000000,0x80000000,0,9 Private key: E656CE5F0FEE7C12CCAAB750AC1E6F9DFE64627F424FF41FEEA9F41AF5EA184E
 BIP44
 Account 0 External 1 m/44'/0'/0'/1/0 -> m/44'/0'/0'/1/10
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,0 Private key: 51A89622142677E81B6AD7F5ED00C339587999DB3942D38F5CDBBB95AAE6DED6
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,1 Private key: 626B96C010C28F58B45E7B08DEA5299BBBE78ED8A19288FEFB1EC293E8AB1053
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,2 Private key: B946AE9B18F97926BB86B2E7089CA67B59C932B00EFA4892080D03EEEADD4C1C
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,3 Private key: 642B0CF182B6DE9A60F97C01C3AA74CED2C03908CAAC9CD1A9002E6C755908F8
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,4 Private key: 68F678808EA93F795A0241C2CF4C2E3F607240AF6C2FE6120FB3D81FB37AF4B1
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,5 Private key: ED5B1F28A9B48ED7A14B0DFB8233AC93D024E54ABB20588F491E4194436AF021
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,6 Private key: 8B19B0F0BE9C3E1D0A988546331A14F9B6B4563E218F830F8CA0CBB5BFA9ED5D
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,7 Private key: D7A23F520A24005B2048DAC9DCEB16E56EE910AB94C5F007D5E84D22BB7C6956
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,8 Private key: B1148E0692FCF0B2C105EDB069FB2F5863C152E744623332CDA4B9885CB2E7E9
 Derivation Path: 0x8000002C,0x80000000,0x80000000,1,9 Private key: 8F4C40D71195A640F2DBD53F590FBBBF0D54A9AF474B861BC575B6944970EAB
 BIP44
 Account 1 External 0 m/44'/0'/1'/0/0 -> m/44'/0'/1'/0/10
  [00:00:01] [Mnemonic: 1] [Addresses: 41] [Speed: 41/s] [F: 0] [hair bleak describe shoot enlist tuition extra pyramid sun scout wheat square]
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,1 Private key: 58F6281655FB5FAD4C9FF6FC5C323700DEECCDF7E11B5A067EE7B074446C9FF2
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,2 Private key: A32A35FB6958A93D02D4E72C8C1C82524203566B4B01A92B535288D792259ADA
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,3 Private key: 9F069E6DE667FA23E61ABBC74497D614C71AA33298BEBE6631A9AD0499B9B4A2
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,4 Private key: 609E28FCBEDF439EBD22838A8E948FE1D5BDA9A92A9B57E71952B62235044044
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,5 Private key: 4B75EDA043DDE46DF1114D5F8A5660A3C253A521BD557E41D628FA421072129E
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,6 Private key: 1A98DACAD1A358716B7953EB0871AAA6350FCB1375DBC11F726F438A10782EDE
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,7 Private key: 5834268A6647BF62D892F9D5456874E59D6118050A23322BAD7DD8F3CFF38FE8
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,8 Private key: F164D31DAA82002DB11C88C3C8413758E3042AD084F5AFBAD93B372CE6DA7534
 Derivation Path: 0x8000002C,0x80000000,0x80000001,0,9 Private key: BB439F32F23134940B1AD27E52C38D00D1A622EF985D445A57291036BE97FA5D
 BIP44
 Account 1 External 1 m/44'/0'/1'/1/0 -> m/44'/0'/1'/1/10
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,0 Private key: 6E61F0FDF756F09FD1BBD25503D02ABFC56180A2E94141D71675722F37F28806
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,1 Private key: 730289122507EA7C4439F99CF1634CCAF0AA120D4B3269F0C0E00834758539D7
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,2 Private key: DFFC4685CF8732428DD63610A584710B2DFEF8E3ADF1FED3E018DC70025E2E1A
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,3 Private key: 1A62BAFAC375D74E7EAE7896074090AD411AC07F7EBCE123EAAB7457F8A38FF8
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,4 Private key: E53956238C287D30254CD5E572F16A2AA7AF11737342626F5A3C65309DCCA836
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,5 Private key: EC999CC7BF4793D5DD68A1F3F29606EED09ED7FC8728D5F4C046C5B460631002
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,6 Private key: CB285695B9F86159C68510B5D44D6F9354DCB75BFB8A46DE823CFA984641E064
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,7 Private key: 55674282E7C6C0879550E81C5135D505B2F6EBD19652F305CCD2DB1E09B6CCA5
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,8 Private key: C29BE9D401136FDEC96D02A8FE938F034249E5133C35F56EC09D95CA8ED6E8C4
 Derivation Path: 0x8000002C,0x80000000,0x80000001,1,9 Private key: 4F2A90BA3FA15F4D595C6B81852E7767D6C1ADFCDBFE258909CF6032B31C7C13
 BIP44 Ethereum
 Account 0 External 0 m/44'/60'/0'/0/0 -> m/44'/60'/0'/0/10
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,0 Private key: FB1B056E3F90282D581ADB578B028B1B7EFF751FA47B8CFF98066100ADD6B276
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,1 Private key: 5F4238515ED4F2A4BBDF7D4EE0B5B000AC14FCA170B8B0E8E970962EF50704BD
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,2 Private key: 65E43A54D7DD660A0A31BB894FBF88458E6A17C7059CE2C2610D89163030CFF5
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,3 Private key: 5947E9B18CE9BB612CDE36EEB9E13CB39EACE7493123402A11A6CFEAB0046DCD
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,4 Private key: 3BE5E4443E946F818DCEC186FA0CD635B99A3A8C4FFEA4407205198B591BAF91
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,5 Private key: 14EB7FDCCA3DF3561B870F7EEC4F4F18566F13430CC20BAF0E54CBEB658801B2
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,6 Private key: A11233778EF9C59285CB775740DB8FF11B6E445E947B34BE016276F0EDFB54E0
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,7 Private key: 5BBA7C11C031643245B775C46E095BF05E67805DF9D14E324C0A5E618021D59F
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,8 Private key: F35DB34EF7D1F5DB8D39361238A04F22B527978801A428E07D725D21B082BC41
 Derivation Path: Derivation Path: 0x8000002C,0x8000003C,0x80000000,0,9 Private key: 52A34EF7CBF5FBE02926E7AD57E248997293C6536ED801026FAB63D7C715D8F4
```
 ## Mode 1
 ## Search for mnemonic words
 - Run CPUs: ```BIP39.exe -t 1 -r 1 -f test.bin``` (Default: language en, 12 words, 10 addresses)
 ### Extra options
 - How many CPU cores to use -t ? (1 - 6(max)) 
 - Language selection -s ? (en, es, ja, it, fr, ko, zh_Hans, zh_Hant)
 - Mnemonic word count -z ? (3, 6, 9, 12, 15, 18, 21, 24)
 - How many addresses to check in each account -n ? (1 - 2000000000)
 - Example ```BIP39.exe -t 6 -r 1 -s fr -z 9 -n 55 -f test.bin```
 ```
C:\Users\user>BIP39.exe -t 6 -r 1 -f test.bin

 BIP39 v1.0 (17.10.2021)

 SEARCH MODE  : COMPRESSED
 DEVICE       : CPU
 CPU THREAD   : 6
 GPU IDS      : 0
 GPU GRIDSIZE : -1x128
 HASH160 FILE : test.bin
 OUTPUT FILE  : Found.txt

 Loading      : 100 %
 Loaded       : 75,471 address

Bloom at 0000018F3A5FD270
  Version     : 2.1
  Entries     : 150942
  Error       : 0.0000010000
  Bits        : 4340363
  Bits/Elem   : 28.755175
  Bytes       : 542546 (0 MB)
  Hash funcs  : 20

  Start Time  : Sun Oct 17 23:52:46 2021

  Mode BIP    : BIP39 -> Bip32 -> Bip44
  Language    : en
  Use words   : 12
  Check       : 10 addresses for each account
  BIP32       : Account 0 m/0/0 -> m/0/10
  BIP32       : Account 1 m/1/0 -> m/1/10
  BIP44       : Account 0 External 0 m/44'/0'/0'/0/0 -> m/44'/0'/0'/0/10
  BIP44       : Account 0 External 1 m/44'/0'/0'/1/0 -> m/44'/0'/0'/1/10
  BIP44       : Account 1 External 0 m/44'/0'/1'/0/0 -> m/44'/0'/1'/0/10
  BIP44       : Account 1 External 1 m/44'/0'/1'/1/0 -> m/44'/0'/1'/1/10
  Site        : https://github.com/phrutis/BIP39
  Donate      : bc1qh2mvnf5fujg93mwl8pe688yucaw9sflmwsukz9

  [00:20:25] [Mnemonic: 3103] [Addresses: 186,047] [Speed: 152/s] [F: 0] [problem chat exercise face between response adjust napkin protect melody fox audit]
  ```
## Building
- Microsoft Visual Studio Community 2019
- CUDA version [**10.22**](https://developer.nvidia.com/cuda-10.2-download-archive?target_os=Windows&target_arch=x86_64&target_version=10&target_type=exenetwork)
## Donation
- BTC: bc1qh2mvnf5fujg93mwl8pe688yucaw9sflmwsukz9
## License
LostCoins is licensed under GPL v3.0
## Disclaimer
ALL THE CODES, PROGRAM AND INFORMATION ARE FOR EDUCATIONAL PURPOSES ONLY. 
USE IT AT YOUR OWN RISK. THE DEVELOPER WILL NOT BE RESPONSIBLE FOR ANY LOSS, DAMAGE OR CLAIM ARISING FROM USING THIS PROGRAM.
