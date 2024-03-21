// SPDX-License-Identifier: GPL-3.0
/*
    Copyright 2021 0KIMS association.

    This file is generated with [snarkJS](https://github.com/iden3/snarkjs).

    snarkJS is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    snarkJS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with snarkJS. If not, see <https://www.gnu.org/licenses/>.
*/

pragma solidity >=0.7.0 <0.9.0;

contract Groth16Verifier {
    // Scalar field size
    uint256 constant r    = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Base field size
    uint256 constant q   = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // Verification Key data
    uint256 constant alphax  = 20491192805390485299153009773594534940189261866228447918068658471970481763042;
    uint256 constant alphay  = 9383485363053290200918347156157836566562967994039712273449902621266178545958;
    uint256 constant betax1  = 4252822878758300859123897981450591353533073413197771768651442665752259397132;
    uint256 constant betax2  = 6375614351688725206403948262868962793625744043794305715222011528459656738731;
    uint256 constant betay1  = 21847035105528745403288232691147584728191162732299865338377159692350059136679;
    uint256 constant betay2  = 10505242626370262277552901082094356697409835680220590971873171140371331206856;
    uint256 constant gammax1 = 11559732032986387107991004021392285783925812861821192530917403151452391805634;
    uint256 constant gammax2 = 10857046999023057135944570762232829481370756359578518086990519993285655852781;
    uint256 constant gammay1 = 4082367875863433681332203403145435568316851327593401208105741076214120093531;
    uint256 constant gammay2 = 8495653923123431417604973247489272438418190587263600148770280649306958101930;
    uint256 constant deltax1 = 3511042253075478516621612090299707496814612786102051248786536765202409777737;
    uint256 constant deltax2 = 19514807879478396193495712911564164707065029832927093412983436809569127968582;
    uint256 constant deltay1 = 18224145646545071906111268954336963219394675931554176001280900512329522109870;
    uint256 constant deltay2 = 1414528849606235285027839697582847815702640009830769377245479606050737818969;

    
    uint256 constant IC0x = 20537889883712698298615438683199475008373149457133736713056888177367664138771;
    uint256 constant IC0y = 12021066772038901800587013160083280397322196141486842440905470983316949080124;
    
    uint256 constant IC1x = 5543359902579343921516941132716085591546621104084206325206329632930792942318;
    uint256 constant IC1y = 4400002357663423712980698936126278330388749312029604267084787782329453951961;
    
    uint256 constant IC2x = 9123119738304725534908510429287517416176506944399418014038731135202970024057;
    uint256 constant IC2y = 21280294816388688042184649991393770227544126937964485242961892852924828239730;
    
    uint256 constant IC3x = 19452189380486789243956295242322257919441211742223789155217585256234941563243;
    uint256 constant IC3y = 2973817467979524795020102665697179612157411855261607448980531147869005725704;
    
    uint256 constant IC4x = 7057258052162490955461144318723950286259296778224040202125612902392706050659;
    uint256 constant IC4y = 14960143678627449088297459584107410715215138774619537497228817011403378124133;
    
    uint256 constant IC5x = 12996120994432445641379022101784669842408867193051264255434923863649790367344;
    uint256 constant IC5y = 21022604752495462425833055846348582675574627155203294256680799001739516101877;
    
    uint256 constant IC6x = 8198714543746339277677899789408579490838604046949021105147532720879424731228;
    uint256 constant IC6y = 5917289159066875353648764397917959885981440634405983178240177930958090296719;
    
    uint256 constant IC7x = 12465824028899365687130469911293975860885396729671467015207255751884037286808;
    uint256 constant IC7y = 20651729025251896951692565006608605751094186507123753045395037557056218847747;
    
    uint256 constant IC8x = 1883812534839683151071581577405036242489244191998080736592693662562895091410;
    uint256 constant IC8y = 5519949289912469195602776247939169505664740662904513428267231032764887833258;
    
    uint256 constant IC9x = 16859487618492927125890541770624201737252639769706062579918502728749253651081;
    uint256 constant IC9y = 3663868349500551311274615185801722349284298619112077901014445973173635315584;
    
    uint256 constant IC10x = 5406930571283851666314551650127544554391531277638799881570445593868003210427;
    uint256 constant IC10y = 20743275209322861526592811127833481134935123082897379812135752780992149353774;
    
    uint256 constant IC11x = 4442150078650560950732743597509398786204718189066007010273939834341921840638;
    uint256 constant IC11y = 9910400237583449132438436218024400616025964066969069710744505425927390745075;
    
    uint256 constant IC12x = 21863268253761609571320716796198829788390675458640495646466040221011763513146;
    uint256 constant IC12y = 12370027507029468571590757908744861131963104649719453829737780782090069825879;
    
    uint256 constant IC13x = 11325429002016437256365658020315467568127813542472857463946408697833494983116;
    uint256 constant IC13y = 19180703954884369008843842031283464521582277014535919224247738001603881665963;
    
    uint256 constant IC14x = 2361198082852288296215682706015239707895609695998434352876088005318569146928;
    uint256 constant IC14y = 5849063956150295298106121229933311327757748445018720952112915549673297442659;
    
    uint256 constant IC15x = 15317459982906465399461931384941742069258793719931449615202973335746035388523;
    uint256 constant IC15y = 19061975935024917615195541110822829703766722585969083565783084310823431341766;
    
    uint256 constant IC16x = 15101717795541526148493992698561310112668578477875629185604492187433782980203;
    uint256 constant IC16y = 18978422231749862433940765454052765030470270826487273635356832657796651033331;
    
    uint256 constant IC17x = 9961187909772375288984060614226808651318638949383353811033690004814125465285;
    uint256 constant IC17y = 18863508098805643438696903664661021946489001264462782216839326459503722764461;
    
    uint256 constant IC18x = 4419051190160889856730912021469722757496542933485150546166167841795834907594;
    uint256 constant IC18y = 18716149899970637570420719357944008315245986535208722663941367927709308327062;
    
    uint256 constant IC19x = 20341066306634144414677929173610361493769470654240200957248998922758628995950;
    uint256 constant IC19y = 396487314933282544067986194897692040200317174577281034444435058593383457820;
    
    uint256 constant IC20x = 6156177785224821200617540280673992613518849183910869050734142750161099170105;
    uint256 constant IC20y = 10616963850918319490192832049170148435491174419836508223938198294084720337200;
    
    uint256 constant IC21x = 5827883978400364607847194299869605604718018100673501593742408972659639422241;
    uint256 constant IC21y = 5531328892082811356707766501706573671180038759265873085348035630383486822361;
    
    uint256 constant IC22x = 4510476591252146013206152122437061507189490939709476247759728137255465943623;
    uint256 constant IC22y = 12917069774647701774599966711219972661463580833678531642510298089600381177646;
    
    uint256 constant IC23x = 14190709931214727839239997485686051287709423641935518983157920746446683428613;
    uint256 constant IC23y = 11597828977049056254420164435260572638358651312690598513098070658094219669798;
    
    uint256 constant IC24x = 4062246696427740498308994720080384737307252806950405939544724671945145831716;
    uint256 constant IC24y = 109274771397822535929127635060727242554087608644781127782710468214323197698;
    
    uint256 constant IC25x = 16814417968235334873310330054433212453202922464515649271112829399440566045915;
    uint256 constant IC25y = 9606997383648630494762352393114731928745951571398073449258077880090029627539;
    
    uint256 constant IC26x = 9131798362016036730606829524570835186503245888736475437987764226539877173228;
    uint256 constant IC26y = 6842404335499130236043083507026661165436095838504535863086482315513574150542;
    
    uint256 constant IC27x = 11254760367184403026203120894163241315137490752576845478361014952371359927995;
    uint256 constant IC27y = 6549273024837572377844892477973479233108594370424594565801154353853881384519;
    
    uint256 constant IC28x = 9877212485079079225372980833042741635701285030064654108074410358027166668502;
    uint256 constant IC28y = 5516881282872962957932513354080540417285845850563080417718911375709566804861;
    
    uint256 constant IC29x = 19027380724669696590897326788926201738986563772077800741029338974189631565339;
    uint256 constant IC29y = 1389141325398853228621661924694050371359209630519554198915575453419000886815;
    
    uint256 constant IC30x = 17228508467483888031891283232038705498318391879067335230074190513773262639628;
    uint256 constant IC30y = 7544594395203373050080648442200067584313194075466159289396288070787995355150;
    
    uint256 constant IC31x = 263785814763900142790607481240011190278563727705339214392103586444781750513;
    uint256 constant IC31y = 16354669799891694589817927570432211123898392133472160958210175604822770156041;
    
    uint256 constant IC32x = 3028416044794925761556103415054436376801665053501562343478041160491480529519;
    uint256 constant IC32y = 19472380058410006197971550811127497620497941626207456045114992447308065535121;
    
    uint256 constant IC33x = 8943326670927888134296120667820740417512447663011418224931264922182375638950;
    uint256 constant IC33y = 13854981609523969200629790507873490199974062131858566661227246299234098009886;
    
    uint256 constant IC34x = 17743795514388780690713961389363596305468471009256072949101498645818683229632;
    uint256 constant IC34y = 13197597368654964128194938757322859823954935687577757461371840810566429563312;
    
    uint256 constant IC35x = 3321608075953699735243360583864389884050547485128158878456543832542414119629;
    uint256 constant IC35y = 5345182311904060029986090720662001767101357617038223301373833064871472073149;
    
    uint256 constant IC36x = 15848343846436025959048416231632884581654065787906159716819465816974203469092;
    uint256 constant IC36y = 12819953301815876078199265613875227680738161841449190465460759430210044380310;
    
    uint256 constant IC37x = 830133101252906024991007830277626286910890441014541889064607536642218535731;
    uint256 constant IC37y = 11884910458340849177573413832631057521967065613029807112361644611426671287911;
    
    uint256 constant IC38x = 5457483422601792203297644346090306250197412850337458882345115121528426305604;
    uint256 constant IC38y = 8772803976057403873256071782059442113805877740923056651430324170180246393040;
    
    uint256 constant IC39x = 19197966781175339561377181955086847705760846880693304341978931140677160844408;
    uint256 constant IC39y = 7013867499273477144409791015848927973036170997221570736303298701180711285428;
    
    uint256 constant IC40x = 19731138171485464643802934968794583449752400050288112747650804629073558320309;
    uint256 constant IC40y = 18404639259419255887117467011969659759135226968477605397395009099800053881643;
    
    uint256 constant IC41x = 15889251713917760146589965374896214299997984805115780921800873296753811035432;
    uint256 constant IC41y = 3557912356764848768495841572080859166793735784919788894931430251487437382405;
    
    uint256 constant IC42x = 2223477185412725451909196182579048336431145887757534056788711275940491738745;
    uint256 constant IC42y = 578260175660766953066488020223223098267689041418511941423400717276502650161;
    
    uint256 constant IC43x = 3984631421020931077617700214919222649052369182339099404936374903893675010203;
    uint256 constant IC43y = 6274612759976414693856316137259463146561164819936031208613636001091408754580;
    
    uint256 constant IC44x = 9400156703061907010128841799126453959732980306221162079703931828560748377914;
    uint256 constant IC44y = 20310606547283519935905768066356351318171270326487647587625458201934066725439;
    
    uint256 constant IC45x = 5124939023457355985105368085306469549133466540673302773490987037830237357263;
    uint256 constant IC45y = 12967748255388594294135048219839736307720645452623294192636804023618270017490;
    
    uint256 constant IC46x = 15545778589103677368844661540416148918902130605778339972817200224857507333147;
    uint256 constant IC46y = 19047516573576937819054299643712889045076794997087640396690001841264117802240;
    
    uint256 constant IC47x = 15251219216798063532861952026799339548038486110734678405048661623247718738852;
    uint256 constant IC47y = 9144377301896307515592867263920750685715313243498389287046261987398162400;
    
    uint256 constant IC48x = 14736561497007704696444460142548763229200857526287723780913275890682502502885;
    uint256 constant IC48y = 3612881216724736602285146164892016107071184909260567053326815043515070343416;
    
    uint256 constant IC49x = 9245571704333407944195400394202152661188672271192198191985261079005523285425;
    uint256 constant IC49y = 13428271728167493588253627030226581378763764103693337378794335496354747138678;
    
    uint256 constant IC50x = 3720202448205993832755666442930182546901387642314531128110557606682261950388;
    uint256 constant IC50y = 9329812283442260007432037072932329591147274389737118469182923831361622935299;
    
    uint256 constant IC51x = 1608810310403997992590469776494062904470402279247472850426298673949135388351;
    uint256 constant IC51y = 873761899770240623760421864892571015750055460148726178956251809015355071645;
    
    uint256 constant IC52x = 6466864080219124311517712419561965646467775545344344985290605564142718445167;
    uint256 constant IC52y = 833094521900354725042507583914639217254235916826773643556694702240785639762;
    
    uint256 constant IC53x = 3195573921092882584027240830390127020465804541422792427699746555367095259598;
    uint256 constant IC53y = 21243634692106355772328714400212290546787924437513168987549843505320983340354;
    
    uint256 constant IC54x = 3930496884137973106752809916394409634053089481756962547466855608059021361694;
    uint256 constant IC54y = 15707505093896961797503618374736156364731114767237714701135873812863447033136;
    
    uint256 constant IC55x = 18032634263300364506491452293252092024688938197829880187878558992132596777361;
    uint256 constant IC55y = 16091705183236563915982415079332288489680412046243762086252905340333412171061;
    
    uint256 constant IC56x = 2153491905675139954463022477783503074919895893325852428063832135620680969623;
    uint256 constant IC56y = 8674653458037959410524380107410085519197405650374496035854368919399745202896;
    
    uint256 constant IC57x = 14805916265289440029432160660931008199335260506925948686564687956079146061942;
    uint256 constant IC57y = 7899437696390259161797300812694980952602375223325114521319818540716505260969;
    
    uint256 constant IC58x = 8803105145479638603077407318827159143352489635408239736254760758377598096569;
    uint256 constant IC58y = 15835516305405480835560674043994372082735193988469413049460098205168299632361;
    
    uint256 constant IC59x = 5914683654419589606241945705320254830145709520792208681982668464827022465065;
    uint256 constant IC59y = 14019204170753691528023828090331015983514980488160058085826057574750645362729;
    
    uint256 constant IC60x = 128120096127617121241739569802626645725238826277730673994886771492315742740;
    uint256 constant IC60y = 9784316704355193174206752107533265087065849745697384856425769406773027341552;
    
    uint256 constant IC61x = 4025611735951036578503548548426941221869353838095957006079379169174426138299;
    uint256 constant IC61y = 5807881319959676320220072812378278528410141900480602565962727713305660144226;
    
    uint256 constant IC62x = 6396524301864777464997852092498388722381532629536850792630309881890083705055;
    uint256 constant IC62y = 2756806064438497563572143066155734364755095339544427988294454558891034117689;
    
    uint256 constant IC63x = 11227243013676947401044491108606952845508175811609727660698299137880686736213;
    uint256 constant IC63y = 21022480992745338303557181260480876630474595314638330215579594104958911558884;
    
    uint256 constant IC64x = 223919207492667155718273080172126990551110204210442852463387329815545515853;
    uint256 constant IC64y = 15334154677535977059860243208531199833765158220746095770088469839665883574569;
    
    uint256 constant IC65x = 15022318650869671727268381210799597448747559857940165819755077579291544798055;
    uint256 constant IC65y = 20861693030929493481399131275199782319531453258021584755728276698885704935617;
    
    uint256 constant IC66x = 20547022126094759966414160056485973107992987654433530145875624031801940150647;
    uint256 constant IC66y = 2639688875149110655640580759515401829043242191813195072366811421886931625139;
    
    uint256 constant IC67x = 11529540629117415257380216985231193673045732333923523264606993347377498543323;
    uint256 constant IC67y = 8247914628987799256757701765358792143009484328833918334546387703630568748620;
    
    uint256 constant IC68x = 19440620657888389673907212671251486776364861993515578154420873466121991218969;
    uint256 constant IC68y = 16126975610853441539956149834275622612006451281441284241385789995149616121442;
    
 
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[68] calldata _pubSignals) public view returns (bool) {
        assembly {
            function checkField(v) {
                if iszero(lt(v, q)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }
            
            // G1 function to multiply a G1 value(x,y) to value in an address
            function g1_mulAccC(pR, x, y, s) {
                let success
                let mIn := mload(0x40)
                mstore(mIn, x)
                mstore(add(mIn, 32), y)
                mstore(add(mIn, 64), s)

                success := staticcall(sub(gas(), 2000), 7, mIn, 96, mIn, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }

                mstore(add(mIn, 64), mload(pR))
                mstore(add(mIn, 96), mload(add(pR, 32)))

                success := staticcall(sub(gas(), 2000), 6, mIn, 128, pR, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            function checkPairing(pA, pB, pC, pubSignals, pMem) -> isOk {
                let _pPairing := add(pMem, pPairing)
                let _pVk := add(pMem, pVk)

                mstore(_pVk, IC0x)
                mstore(add(_pVk, 32), IC0y)

                // Compute the linear combination vk_x
                
                g1_mulAccC(_pVk, IC1x, IC1y, calldataload(add(pubSignals, 0)))
                
                g1_mulAccC(_pVk, IC2x, IC2y, calldataload(add(pubSignals, 32)))
                
                g1_mulAccC(_pVk, IC3x, IC3y, calldataload(add(pubSignals, 64)))
                
                g1_mulAccC(_pVk, IC4x, IC4y, calldataload(add(pubSignals, 96)))
                
                g1_mulAccC(_pVk, IC5x, IC5y, calldataload(add(pubSignals, 128)))
                
                g1_mulAccC(_pVk, IC6x, IC6y, calldataload(add(pubSignals, 160)))
                
                g1_mulAccC(_pVk, IC7x, IC7y, calldataload(add(pubSignals, 192)))
                
                g1_mulAccC(_pVk, IC8x, IC8y, calldataload(add(pubSignals, 224)))
                
                g1_mulAccC(_pVk, IC9x, IC9y, calldataload(add(pubSignals, 256)))
                
                g1_mulAccC(_pVk, IC10x, IC10y, calldataload(add(pubSignals, 288)))
                
                g1_mulAccC(_pVk, IC11x, IC11y, calldataload(add(pubSignals, 320)))
                
                g1_mulAccC(_pVk, IC12x, IC12y, calldataload(add(pubSignals, 352)))
                
                g1_mulAccC(_pVk, IC13x, IC13y, calldataload(add(pubSignals, 384)))
                
                g1_mulAccC(_pVk, IC14x, IC14y, calldataload(add(pubSignals, 416)))
                
                g1_mulAccC(_pVk, IC15x, IC15y, calldataload(add(pubSignals, 448)))
                
                g1_mulAccC(_pVk, IC16x, IC16y, calldataload(add(pubSignals, 480)))
                
                g1_mulAccC(_pVk, IC17x, IC17y, calldataload(add(pubSignals, 512)))
                
                g1_mulAccC(_pVk, IC18x, IC18y, calldataload(add(pubSignals, 544)))
                
                g1_mulAccC(_pVk, IC19x, IC19y, calldataload(add(pubSignals, 576)))
                
                g1_mulAccC(_pVk, IC20x, IC20y, calldataload(add(pubSignals, 608)))
                
                g1_mulAccC(_pVk, IC21x, IC21y, calldataload(add(pubSignals, 640)))
                
                g1_mulAccC(_pVk, IC22x, IC22y, calldataload(add(pubSignals, 672)))
                
                g1_mulAccC(_pVk, IC23x, IC23y, calldataload(add(pubSignals, 704)))
                
                g1_mulAccC(_pVk, IC24x, IC24y, calldataload(add(pubSignals, 736)))
                
                g1_mulAccC(_pVk, IC25x, IC25y, calldataload(add(pubSignals, 768)))
                
                g1_mulAccC(_pVk, IC26x, IC26y, calldataload(add(pubSignals, 800)))
                
                g1_mulAccC(_pVk, IC27x, IC27y, calldataload(add(pubSignals, 832)))
                
                g1_mulAccC(_pVk, IC28x, IC28y, calldataload(add(pubSignals, 864)))
                
                g1_mulAccC(_pVk, IC29x, IC29y, calldataload(add(pubSignals, 896)))
                
                g1_mulAccC(_pVk, IC30x, IC30y, calldataload(add(pubSignals, 928)))
                
                g1_mulAccC(_pVk, IC31x, IC31y, calldataload(add(pubSignals, 960)))
                
                g1_mulAccC(_pVk, IC32x, IC32y, calldataload(add(pubSignals, 992)))
                
                g1_mulAccC(_pVk, IC33x, IC33y, calldataload(add(pubSignals, 1024)))
                
                g1_mulAccC(_pVk, IC34x, IC34y, calldataload(add(pubSignals, 1056)))
                
                g1_mulAccC(_pVk, IC35x, IC35y, calldataload(add(pubSignals, 1088)))
                
                g1_mulAccC(_pVk, IC36x, IC36y, calldataload(add(pubSignals, 1120)))
                
                g1_mulAccC(_pVk, IC37x, IC37y, calldataload(add(pubSignals, 1152)))
                
                g1_mulAccC(_pVk, IC38x, IC38y, calldataload(add(pubSignals, 1184)))
                
                g1_mulAccC(_pVk, IC39x, IC39y, calldataload(add(pubSignals, 1216)))
                
                g1_mulAccC(_pVk, IC40x, IC40y, calldataload(add(pubSignals, 1248)))
                
                g1_mulAccC(_pVk, IC41x, IC41y, calldataload(add(pubSignals, 1280)))
                
                g1_mulAccC(_pVk, IC42x, IC42y, calldataload(add(pubSignals, 1312)))
                
                g1_mulAccC(_pVk, IC43x, IC43y, calldataload(add(pubSignals, 1344)))
                
                g1_mulAccC(_pVk, IC44x, IC44y, calldataload(add(pubSignals, 1376)))
                
                g1_mulAccC(_pVk, IC45x, IC45y, calldataload(add(pubSignals, 1408)))
                
                g1_mulAccC(_pVk, IC46x, IC46y, calldataload(add(pubSignals, 1440)))
                
                g1_mulAccC(_pVk, IC47x, IC47y, calldataload(add(pubSignals, 1472)))
                
                g1_mulAccC(_pVk, IC48x, IC48y, calldataload(add(pubSignals, 1504)))
                
                g1_mulAccC(_pVk, IC49x, IC49y, calldataload(add(pubSignals, 1536)))
                
                g1_mulAccC(_pVk, IC50x, IC50y, calldataload(add(pubSignals, 1568)))
                
                g1_mulAccC(_pVk, IC51x, IC51y, calldataload(add(pubSignals, 1600)))
                
                g1_mulAccC(_pVk, IC52x, IC52y, calldataload(add(pubSignals, 1632)))
                
                g1_mulAccC(_pVk, IC53x, IC53y, calldataload(add(pubSignals, 1664)))
                
                g1_mulAccC(_pVk, IC54x, IC54y, calldataload(add(pubSignals, 1696)))
                
                g1_mulAccC(_pVk, IC55x, IC55y, calldataload(add(pubSignals, 1728)))
                
                g1_mulAccC(_pVk, IC56x, IC56y, calldataload(add(pubSignals, 1760)))
                
                g1_mulAccC(_pVk, IC57x, IC57y, calldataload(add(pubSignals, 1792)))
                
                g1_mulAccC(_pVk, IC58x, IC58y, calldataload(add(pubSignals, 1824)))
                
                g1_mulAccC(_pVk, IC59x, IC59y, calldataload(add(pubSignals, 1856)))
                
                g1_mulAccC(_pVk, IC60x, IC60y, calldataload(add(pubSignals, 1888)))
                
                g1_mulAccC(_pVk, IC61x, IC61y, calldataload(add(pubSignals, 1920)))
                
                g1_mulAccC(_pVk, IC62x, IC62y, calldataload(add(pubSignals, 1952)))
                
                g1_mulAccC(_pVk, IC63x, IC63y, calldataload(add(pubSignals, 1984)))
                
                g1_mulAccC(_pVk, IC64x, IC64y, calldataload(add(pubSignals, 2016)))
                
                g1_mulAccC(_pVk, IC65x, IC65y, calldataload(add(pubSignals, 2048)))
                
                g1_mulAccC(_pVk, IC66x, IC66y, calldataload(add(pubSignals, 2080)))
                
                g1_mulAccC(_pVk, IC67x, IC67y, calldataload(add(pubSignals, 2112)))
                
                g1_mulAccC(_pVk, IC68x, IC68y, calldataload(add(pubSignals, 2144)))
                

                // -A
                mstore(_pPairing, calldataload(pA))
                mstore(add(_pPairing, 32), mod(sub(q, calldataload(add(pA, 32))), q))

                // B
                mstore(add(_pPairing, 64), calldataload(pB))
                mstore(add(_pPairing, 96), calldataload(add(pB, 32)))
                mstore(add(_pPairing, 128), calldataload(add(pB, 64)))
                mstore(add(_pPairing, 160), calldataload(add(pB, 96)))

                // alpha1
                mstore(add(_pPairing, 192), alphax)
                mstore(add(_pPairing, 224), alphay)

                // beta2
                mstore(add(_pPairing, 256), betax1)
                mstore(add(_pPairing, 288), betax2)
                mstore(add(_pPairing, 320), betay1)
                mstore(add(_pPairing, 352), betay2)

                // vk_x
                mstore(add(_pPairing, 384), mload(add(pMem, pVk)))
                mstore(add(_pPairing, 416), mload(add(pMem, add(pVk, 32))))


                // gamma2
                mstore(add(_pPairing, 448), gammax1)
                mstore(add(_pPairing, 480), gammax2)
                mstore(add(_pPairing, 512), gammay1)
                mstore(add(_pPairing, 544), gammay2)

                // C
                mstore(add(_pPairing, 576), calldataload(pC))
                mstore(add(_pPairing, 608), calldataload(add(pC, 32)))

                // delta2
                mstore(add(_pPairing, 640), deltax1)
                mstore(add(_pPairing, 672), deltax2)
                mstore(add(_pPairing, 704), deltay1)
                mstore(add(_pPairing, 736), deltay2)


                let success := staticcall(sub(gas(), 2000), 8, _pPairing, 768, _pPairing, 0x20)

                isOk := and(success, mload(_pPairing))
            }

            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))

            // Validate that all evaluations ∈ F
            
            checkField(calldataload(add(_pubSignals, 0)))
            
            checkField(calldataload(add(_pubSignals, 32)))
            
            checkField(calldataload(add(_pubSignals, 64)))
            
            checkField(calldataload(add(_pubSignals, 96)))
            
            checkField(calldataload(add(_pubSignals, 128)))
            
            checkField(calldataload(add(_pubSignals, 160)))
            
            checkField(calldataload(add(_pubSignals, 192)))
            
            checkField(calldataload(add(_pubSignals, 224)))
            
            checkField(calldataload(add(_pubSignals, 256)))
            
            checkField(calldataload(add(_pubSignals, 288)))
            
            checkField(calldataload(add(_pubSignals, 320)))
            
            checkField(calldataload(add(_pubSignals, 352)))
            
            checkField(calldataload(add(_pubSignals, 384)))
            
            checkField(calldataload(add(_pubSignals, 416)))
            
            checkField(calldataload(add(_pubSignals, 448)))
            
            checkField(calldataload(add(_pubSignals, 480)))
            
            checkField(calldataload(add(_pubSignals, 512)))
            
            checkField(calldataload(add(_pubSignals, 544)))
            
            checkField(calldataload(add(_pubSignals, 576)))
            
            checkField(calldataload(add(_pubSignals, 608)))
            
            checkField(calldataload(add(_pubSignals, 640)))
            
            checkField(calldataload(add(_pubSignals, 672)))
            
            checkField(calldataload(add(_pubSignals, 704)))
            
            checkField(calldataload(add(_pubSignals, 736)))
            
            checkField(calldataload(add(_pubSignals, 768)))
            
            checkField(calldataload(add(_pubSignals, 800)))
            
            checkField(calldataload(add(_pubSignals, 832)))
            
            checkField(calldataload(add(_pubSignals, 864)))
            
            checkField(calldataload(add(_pubSignals, 896)))
            
            checkField(calldataload(add(_pubSignals, 928)))
            
            checkField(calldataload(add(_pubSignals, 960)))
            
            checkField(calldataload(add(_pubSignals, 992)))
            
            checkField(calldataload(add(_pubSignals, 1024)))
            
            checkField(calldataload(add(_pubSignals, 1056)))
            
            checkField(calldataload(add(_pubSignals, 1088)))
            
            checkField(calldataload(add(_pubSignals, 1120)))
            
            checkField(calldataload(add(_pubSignals, 1152)))
            
            checkField(calldataload(add(_pubSignals, 1184)))
            
            checkField(calldataload(add(_pubSignals, 1216)))
            
            checkField(calldataload(add(_pubSignals, 1248)))
            
            checkField(calldataload(add(_pubSignals, 1280)))
            
            checkField(calldataload(add(_pubSignals, 1312)))
            
            checkField(calldataload(add(_pubSignals, 1344)))
            
            checkField(calldataload(add(_pubSignals, 1376)))
            
            checkField(calldataload(add(_pubSignals, 1408)))
            
            checkField(calldataload(add(_pubSignals, 1440)))
            
            checkField(calldataload(add(_pubSignals, 1472)))
            
            checkField(calldataload(add(_pubSignals, 1504)))
            
            checkField(calldataload(add(_pubSignals, 1536)))
            
            checkField(calldataload(add(_pubSignals, 1568)))
            
            checkField(calldataload(add(_pubSignals, 1600)))
            
            checkField(calldataload(add(_pubSignals, 1632)))
            
            checkField(calldataload(add(_pubSignals, 1664)))
            
            checkField(calldataload(add(_pubSignals, 1696)))
            
            checkField(calldataload(add(_pubSignals, 1728)))
            
            checkField(calldataload(add(_pubSignals, 1760)))
            
            checkField(calldataload(add(_pubSignals, 1792)))
            
            checkField(calldataload(add(_pubSignals, 1824)))
            
            checkField(calldataload(add(_pubSignals, 1856)))
            
            checkField(calldataload(add(_pubSignals, 1888)))
            
            checkField(calldataload(add(_pubSignals, 1920)))
            
            checkField(calldataload(add(_pubSignals, 1952)))
            
            checkField(calldataload(add(_pubSignals, 1984)))
            
            checkField(calldataload(add(_pubSignals, 2016)))
            
            checkField(calldataload(add(_pubSignals, 2048)))
            
            checkField(calldataload(add(_pubSignals, 2080)))
            
            checkField(calldataload(add(_pubSignals, 2112)))
            
            checkField(calldataload(add(_pubSignals, 2144)))
            
            checkField(calldataload(add(_pubSignals, 2176)))
            

            // Validate all evaluations
            let isValid := checkPairing(_pA, _pB, _pC, _pubSignals, pMem)

            mstore(0, isValid)
             return(0, 0x20)
         }
     }
 }
