open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module AdventOfCode.One.Input where

open import String.ASCII

open import Agda.Builtin.Char
open import Agda.Builtin.Char.Properties
open import Agda.Builtin.String

input : String
input =
  "a  b
c  d"
  -- "39472   15292
  --  41795   28867
  --  66901   41393
  --  49097   61173
  --  56143   52888
  --  95316   12022
  --  12479   41393
  --  44746   54563
  --  75154   45829
  --  11303   70489
  --  34369   42303
  --  19787   10318
  --  57355   54563
  --  17649   78041
  --  78041   90912
  --  42025   70838
  --  83962   27416
  --  58852   60140
  --  10900   78041
  --  81682   86361
  --  73646   59340
  --  69559   52888
  --  11792   37020
  --  16986   60140
  --  64640   99547
  --  72905   79616
  --  49132   68436
  --  60004   25440
  --  83058   36384
  --  56218   51713
  --  42752   85502
  --  53210   25564
  --  97525   46775
  --  85200   81707
  --  93134   17917
  --  92436   29703
  --  43282   26102
  --  56561   17917
  --  38517   60140
  --  21394   11537
  --  22870   56891
  --  91081   75176
  --  58106   60279
  --  31335   96310
  --  32992   60140
  --  38454   54563
  --  33694   74901
  --  18307   90620
  --  34138   37678
  --  30210   35783
  --  25191   15227
  --  47869   11537
  --  51431   99893
  --  59221   57034
  --  67820   46594
  --  25286   65918
  --  49630   64107
  --  49512   23996
  --  75253   19155
  --  91755   44731
  --  84331   14322
  --  10777   45829
  --  44531   31325
  --  44387   44368
  --  22092   78828
  --  62647   74552
  --  73962   61652
  --  70872   38663
  --  41669   17917
  --  36394   39664
  --  86666   32126
  --  94564   71364
  --  86975   65813
  --  80625   26674
  --  60822   44368
  --  70000   88293
  --  22902   68436
  --  14424   12070
  --  49549   76372
  --  98327   15292
  --  16200   41393
  --  75176   59283
  --  87545   56534
  --  52574   42041
  --  89909   82203
  --  59362   25776
  --  31396   65918
  --  23097   67302
  --  16639   73771
  --  88531   61423
  --  96093   57034
  --  66284   27416
  --  66985   80547
  --  49619   82916
  --  15828   96310
  --  64988   54786
  --  21667   65918
  --  74847   53532
  --  80596   74328
  --  63472   77634
  --  38623   37355
  --  38050   77634
  --  57186   77092
  --  32231   96310
  --  53056   85502
  --  99616   27723
  --  44092   39113
  --  28177   73886
  --  43152   71052
  --  63504   85873
  --  82199   13631
  --  16827   95980
  --  12662   94593
  --  15202   19317
  --  11297   44368
  --  75181   23789
  --  82671   11537
  --  27416   28613
  --  32617   17917
  --  32093   56597
  --  43092   81496
  --  98048   38603
  --  33815   94399
  --  49197   75323
  --  72360   38805
  --  12218   57034
  --  79339   25820
  --  55769   11065
  --  24748   33341
  --  73771   85800
  --  33005   51346
  --  53234   37678
  --  35799   99893
  --  67715   72495
  --  39385   60140
  --  80517   67721
  --  23083   27416
  --  35643   34652
  --  20015   85084
  --  54047   68436
  --  90892   27416
  --  83304   45829
  --  52334   42025
  --  22737   48971
  --  44841   85502
  --  54440   88682
  --  59337   44466
  --  86226   44368
  --  79865   23789
  --  92432   25313
  --  16492   46594
  --  77422   38673
  --  93057   23789
  --  27428   87965
  --  91111   85502
  --  16734   96310
  --  92704   91204
  --  71080   32126
  --  79064   38805
  --  21521   98343
  --  14447   42025
  --  88341   78869
  --  13881   64574
  --  98689   57609
  --  96688   20324
  --  83204   66011
  --  30155   78041
  --  79383   57771
  --  66777   42501
  --  79365   29078
  --  38302   85502
  --  59476   41393
  --  12235   97187
  --  79638   13709
  --  12734   77092
  --  26482   96310
  --  53709   38414
  --  78983   68436
  --  56875   32126
  --  34652   79445
  --  47807   44368
  --  20838   37678
  --  77644   42695
  --  91040   34471
  --  19857   38805
  --  37257   19299
  --  84323   45829
  --  45765   27807
  --  80010   17917
  --  50993   17917
  --  87739   17917
  --  21074   83774
  --  21486   65838
  --  85062   65414
  --  64425   60832
  --  46875   72398
  --  77011   94090
  --  16732   14509
  --  63302   48158
  --  96936   81496
  --  54563   77092
  --  32946   37678
  --  57558   40189
  --  77371   20945
  --  70922   27416
  --  34893   44368
  --  20064   61173
  --  42298   26409
  --  50286   87965
  --  37070   28219
  --  25648   15174
  --  72425   49204
  --  70118   23789
  --  43832   54563
  --  40026   23789
  --  20922   60128
  --  85906   96310
  --  62704   75007
  --  14096   81496
  --  27162   56750
  --  93880   67721
  --  61173   16445
  --  73917   75176
  --  95980   77092
  --  89429   38668
  --  95730   32268
  --  99893   54563
  --  87309   76137
  --  74425   11641
  --  96310   90444
  --  76188   96310
  --  50165   37678
  --  80206   36550
  --  64022   73771
  --  65510   95980
  --  71848   87965
  --  79418   95980
  --  52569   85502
  --  89371   99893
  --  68344   73771
  --  19148   81496
  --  83338   34652
  --  15292   64493
  --  50026   85502
  --  46923   42025
  --  65318   36031
  --  84727   65918
  --  12709   19317
  --  49025   13484
  --  45423   65918
  --  71561   56750
  --  70652   95980
  --  49677   67721
  --  87744   15824
  --  68616   77092
  --  56750   98610
  --  27368   15292
  --  96635   72495
  --  82682   86884
  --  49305   22888
  --  57058   76493
  --  71872   15292
  --  37337   99893
  --  49141   27416
  --  58652   59221
  --  68121   59924
  --  15655   27416
  --  62826   52888
  --  21376   13478
  --  90582   73415
  --  15256   83645
  --  75807   77837
  --  25162   67721
  --  20898   69247
  --  92171   40775
  --  32584   57034
  --  68026   65918
  --  89047   81496
  --  77634   16657
  --  76187   67862
  --  34375   68115
  --  17970   36680
  --  73342   11537
  --  88262   68436
  --  85191   41393
  --  13235   74763
  --  84522   26546
  --  24204   83774
  --  50892   44388
  --  73708   45829
  --  20453   35352
  --  17601   54563
  --  72728   31817
  --  53568   77092
  --  51327   87796
  --  32562   45829
  --  57528   73771
  --  65476   62414
  --  87452   38805
  --  27996   67569
  --  20039   42216
  --  46643   62818
  --  52888   37678
  --  78679   89549
  --  40854   47456
  --  83512   83774
  --  40653   19984
  --  15653   87965
  --  24606   28934
  --  31608   43847
  --  15608   87965
  --  44105   78041
  --  51928   21069
  --  33215   11537
  --  13283   56032
  --  99082   34188
  --  52093   96310
  --  61555   22523
  --  42163   59313
  --  70384   21347
  --  68901   14849
  --  45947   68914
  --  43211   17917
  --  49277   42695
  --  34180   83406
  --  92846   50278
  --  79167   38805
  --  20193   77092
  --  20458   44368
  --  32126   81496
  --  66236   83382
  --  12738   28293
  --  44729   99893
  --  69671   86850
  --  83285   58736
  --  56016   96747
  --  99469   68436
  --  93215   19776
  --  25585   44206
  --  53706   83774
  --  87427   59088
  --  46185   56750
  --  36420   42025
  --  75640   12667
  --  62041   58764
  --  29681   37678
  --  52824   41716
  --  89079   32126
  --  99760   84744
  --  96415   38301
  --  63171   23789
  --  29436   16140
  --  83447   73771
  --  75739   11537
  --  82453   65918
  --  84569   65918
  --  21534   77172
  --  12101   74770
  --  77859   42695
  --  52861   85502
  --  35871   21725
  --  42076   39498
  --  27769   65918
  --  42055   60140
  --  15647   46042
  --  71930   43847
  --  64803   48360
  --  57132   72709
  --  86112   88764
  --  32257   35904
  --  65077   15267
  --  26467   43122
  --  16903   22211
  --  90305   42025
  --  40337   91440
  --  88470   45958
  --  25305   98303
  --  96579   89051
  --  79525   73920
  --  41786   95980
  --  67337   20284
  --  18437   60448
  --  24149   18786
  --  90518   60165
  --  61117   68317
  --  47404   89642
  --  70455   43847
  --  42695   30003
  --  32127   63953
  --  71650   35205
  --  25690   60128
  --  99806   68436
  --  46357   39579
  --  74131   46594
  --  47895   47800
  --  26468   43847
  --  41393   15292
  --  70792   96310
  --  64983   72495
  --  14730   75176
  --  67663   97315
  --  79374   31240
  --  69026   83411
  --  22680   23789
  --  71431   27416
  --  77808   21074
  --  22211   70174
  --  98616   17996
  --  92938   38805
  --  89127   85502
  --  51477   87965
  --  90677   99208
  --  59730   77092
  --  98858   84528
  --  30238   83774
  --  75429   87965
  --  27930   37678
  --  14348   52888
  --  16626   68436
  --  71073   65918
  --  41699   44368
  --  97130   26865
  --  17234   64748
  --  19638   73771
  --  32507   38805
  --  70053   43714
  --  74550   11537
  --  32214   89987
  --  58219   74181
  --  94952   15292
  --  33006   61173
  --  47639   45559
  --  40240   72346
  --  25466   73771
  --  91357   54563
  --  34918   44368
  --  36904   57034
  --  82039   60128
  --  83050   27542
  --  33904   36886
  --  49071   77634
  --  29378   68436
  --  31555   17917
  --  10652   44368
  --  38017   98107
  --  61056   61173
  --  14038   22737
  --  23926   14836
  --  87700   17917
  --  27680   67320
  --  17606   20744
  --  71665   38805
  --  73591   90610
  --  75931   23789
  --  45829   13721
  --  11852   62648
  --  82002   43847
  --  18278   11819
  --  76392   78041
  --  12128   92298
  --  39019   24002
  --  29212   78830
  --  70049   96310
  --  97782   75559
  --  93518   42025
  --  24972   68164
  --  79331   82197
  --  53946   63209
  --  29692   36006
  --  90018   47044
  --  80392   94377
  --  36656   49166
  --  71114   96458
  --  58048   34652
  --  41279   38805
  --  52537   41393
  --  33546   39103
  --  70780   60140
  --  36455   62146
  --  87797   11284
  --  21614   83774
  --  87965   65918
  --  84530   87965
  --  31327   60140
  --  18367   73575
  --  64436   15292
  --  20247   99322
  --  33510   34652
  --  38591   60472
  --  26569   34652
  --  95619   32751
  --  75902   15292
  --  13377   27416
  --  67381   85502
  --  33665   27308
  --  49639   27416
  --  41023   11537
  --  25245   21668
  --  88275   89008
  --  86587   90992
  --  77709   68436
  --  49679   89471
  --  84751   42695
  --  89970   60140
  --  35926   60128
  --  29813   42025
  --  37865   72495
  --  16156   60194
  --  27868   76472
  --  77973   75176
  --  22695   79830
  --  58595   56952
  --  95239   96639
  --  71032   95980
  --  91716   75176
  --  78993   43847
  --  99915   98469
  --  97751   11537
  --  85502   60039
  --  50198   68602
  --  63219   28654
  --  65281   95499
  --  59926   63079
  --  90344   17917
  --  84508   68436
  --  11497   53277
  --  23204   60128
  --  23323   44368
  --  59901   82429
  --  40780   54563
  --  86228   77092
  --  15570   92416
  --  30888   63270
  --  13324   60221
  --  69364   15292
  --  95308   87722
  --  60190   92919
  --  99873   76986
  --  14117   75176
  --  93167   42025
  --  31214   26740
  --  63953   75176
  --  16764   87965
  --  53411   18481
  --  23762   20430
  --  62056   95980
  --  72495   72495
  --  77818   55142
  --  87870   41393
  --  38763   72435
  --  95817   27379
  --  73572   71492
  --  86836   15292
  --  67571   55135
  --  84424   68436
  --  38842   33961
  --  25252   99893
  --  52969   60128
  --  75457   98187
  --  15405   56750
  --  85810   34652
  --  52562   40472
  --  26458   87835
  --  57049   12947
  --  92406   43679
  --  71405   15292
  --  13004   24537
  --  26183   19467
  --  57431   44368
  --  49655   87965
  --  61580   52775
  --  50127   68060
  --  22900   37678
  --  82172   73771
  --  64722   44368
  --  20817   27416
  --  29505   94508
  --  83118   42025
  --  11609   73771
  --  91300   50758
  --  12871   69985
  --  76642   85502
  --  59612   45829
  --  22493   21789
  --  97865   28573
  --  38509   42695
  --  62726   22786
  --  97473   60140
  --  11612   72495
  --  22478   94640
  --  78811   58753
  --  57737   91274
  --  96232   94576
  --  97572   81557
  --  82900   32111
  --  19759   70364
  --  72856   63532
  --  96772   39170
  --  23639   34568
  --  51369   85502
  --  57419   77634
  --  26364   26509
  --  75781   74064
  --  18008   75570
  --  90125   23030
  --  28428   38805
  --  33799   68436
  --  81411   99893
  --  32078   27808
  --  79975   83566
  --  52755   69516
  --  57264   49914
  --  64517   17917
  --  73224   32126
  --  35194   46594
  --  56603   22108
  --  19967   84231
  --  77598   41393
  --  48288   85502
  --  59468   85296
  --  47471   60128
  --  92962   87965
  --  33647   54992
  --  40482   83774
  --  54705   45831
  --  68436   40140
  --  83774   16001
  --  50181   56750
  --  46534   37678
  --  73109   83774
  --  14691   72139
  --  45203   18499
  --  93717   41393
  --  90942   61173
  --  93639   96310
  --  43230   81496
  --  35162   81496
  --  99850   74025
  --  86446   27902
  --  83395   77092
  --  34567   42695
  --  38120   75176
  --  43847   15292
  --  18314   93498
  --  35219   43847
  --  57034   68631
  --  65653   31365
  --  63354   20793
  --  57162   43136
  --  82266   44368
  --  12486   98890
  --  95955   63953
  --  84375   34652
  --  86891   38805
  --  30860   34652
  --  39153   72495
  --  60323   23789
  --  54199   15292
  --  56072   56750
  --  93245   57078
  --  76450   43847
  --  59767   54737
  --  68416   85814
  --  37507   52294
  --  95599   37678
  --  26535   82789
  --  24134   75314
  --  44403   73771
  --  98864   37678
  --  65407   46261
  --  79131   19317
  --  13530   17917
  --  65218   14610
  --  25382   22670
  --  92220   75176
  --  85985   59377
  --  70302   24147
  --  64121   64263
  --  67721   96310
  --  23443   43847
  --  84136   34307
  --  63440   59221
  --  53644   63953
  --  55702   45127
  --  38805   68295
  --  85325   50302
  --  23500   28669
  --  69804   52427
  --  84397   22809
  --  27004   85502
  --  37093   29693
  --  96090   45829
  --  94277   65918
  --  75959   20621
  --  14695   69851
  --  21277   99893
  --  25052   65918
  --  62281   23789
  --  28206   11537
  --  61780   38805
  --  43950   43399
  --  77501   40253
  --  73366   47747
  --  24723   53159
  --  18309   29185
  --  88351   87965
  --  32451   87965
  --  27961   82138
  --  15868   23052
  --  83064   81496
  --  68951   11537
  --  97293   50439
  --  56831   57301
  --  80363   47574
  --  33684   60128
  --  10701   20752
  --  42064   36397
  --  69486   96133
  --  47015   99893
  --  29202   42695
  --  82115   23789
  --  95165   52036
  --  57418   47142
  --  67506   38805
  --  58868   87965
  --  74165   44368
  --  30214   83774
  --  83623   17917
  --  17331   68436
  --  30459   14907
  --  67434   65918
  --  40727   90836
  --  61581   93472
  --  33819   63953
  --  49763   86280
  --  97486   67721
  --  26812   33295
  --  12336   43847
  --  18378   73771
  --  84937   99191
  --  35224   65918
  --  49694   27416
  --  49529   78672
  --  18201   35773
  --  74497   46594
  --  68037   34652
  --  36953   68436
  --  85485   92527
  --  88430   99893
  --  71498   83659
  --  60128   23848
  --  96672   27416
  --  64061   79790
  --  59825   54563
  --  74366   68436
  --  41534   11537
  --  87667   21591
  --  10150   75176
  --  44315   45829
  --  14678   42695
  --  72111   96310
  --  58956   23680
  --  69294   42025
  --  20619   57034
  --  37843   27416
  --  29529   27615
  --  19702   83774
  --  32072   14710
  --  50568   11537
  --  51287   85502
  --  94333   32126
  --  18585   34938
  --  23789   61804
  --  46594   77092
  --  79106   26759
  --  41356   96103
  --  10594   81496
  --  11595   59026
  --  98318   49115
  --  13672   15783
  --  13257   42025
  --  72928   26741
  --  93735   52496
  --  53663   34203
  --  58872   52888
  --  65915   99893
  --  75718   58779
  --  38451   39438
  --  35425   27416
  --  12378   93586
  --  91509   97927
  --  56599   27778
  --  44971   57034
  --  21719   65918
  --  20336   93128
  --  18110   46594
  --  99088   60128
  --  85957   97300
  --  32492   42695
  --  43009   96238
  --  70212   31422
  --  34312   11537
  --  61916   42723
  --  51817   11537
  --  72892   90401
  --  32753   99893
  --  54502   62779
  --  39127   48368
  --  13434   51199
  --  44413   20326
  --  32900   68436
  --  65505   83774
  --  83501   87965
  --  50906   36556
  --  61014   44368
  --  95454   75176
  --  77008   41393
  --  58087   75176
  --  69905   93067
  --  37788   59221
  --  31700   42326
  --  78758   15292
  --  60428   95980
  --  82953   34652
  --  57964   63113
  --  11094   96310
  --  64195   19317
  --  52961   80659
  --  36007   54563
  --  75733   54563
  --  25387   76167
  --  11537   65918
  --  60140   17917
  --  45111   15292
  --  99999   67189
  --  63747   11537
  --  20625   43214
  --  92339   10979
  --  24864   38805
  --  26017   79424
  --  57414   95980
  --  63707   17917
  --  88020   54563
  --  37973   29335
  --  30076   87838
  --  52584   65918
  --  49038   25377
  --  61582   83162
  --  21115   86682
  --  67207   68436
  --  74877   15341
  --  44094   99893
  --  41244   26837
  --  84493   97732
  --  61793   97981
  --  28185   67721
  --  18529   23789
  --  53238   80962
  --  56830   34020
  --  42491   37938
  --  44708   77092
  --  54024   23873
  --  81496   20953
  --  23812   37678
  --  86480   44368
  --  68399   47559
  --  35185   75176
  --  37233   33363
  --  75966   83774
  --  54671   15292
  --  39056   21920
  --  55159   60140
  --  70822   21845
  --  43695   56792
  --  46035   37430
  --  44197   81496
  --  72777   99476
  --  36610   97933
  --  69757   15287
  --  87912   83774
  --  34679   83581
  --  34931   15292
  --  93254   71634
  --  64175   45693
  --  87296   75176
  --  94232   17596
  --  93856   68436
  --  44368   15292
  --  93430   11537
  --  51742   31698
  --  37653   85502
  --  83663   94306
  --  28522   93651
  --  94057   22959
  --  64826   94855
  --  42079   99893
  --  79925   26385
  --  74592   25770
  --  20675   72495
  --  65728   50739
  --  92462   59954
  --  23381   77025
  --  44104   65121
  --  48953   81496
  --  37678   46594
  --  63422   89239
  --  49735   35632
  --  85048   71538
  --  19402   81496
  --  86874   45829
  --  73564   45829
  --  74511   64584
  --  17917   29104
  --  53604   13639
  --  13699   12819
  --  42901   71544
  --  64254   65918
  --  42770   45829
  --  96114   44368
  --  93782   56750
  --  57646   90086
  --  46334   49872
  --  63175   54563
  --  98847   47091
  --  15551   22124
  --  91269   83774
  --  42322   96310
  --  99400   32126
  --  29079   65918
  --  51358   42025
  --  57109   22211
  --  75643   19675
  --  50779   42100
  --  68902   61940
  --  91483   15861
  --  72751   95639
  --  22226   75719
  --  30515   37678
  --  44941   94189
  --  60907   78041
  --  96158   41829
  --  58058   99893
  --  20085   37678
  --  78405   88266
  --  47918   87965
  --  76270   42402
  --  60874   87102
  --  74798   23789
  --  89867   43847
  --  21013   95168
  --  50155   73771
  --  96922   60329
  --  73275   54563
  --  85392   98615
  --  69178   91775
  --  26665   49635
  --  41944   41525
  --  48235   82994
  --  74950   61557
  --  60869   73771
  --  19317   15074
  --  28433   68991
  --  27814   90764
  --  62468   41393
  --  71778   92876
  --  19383   57314
  --  74225   72460
  --  45257   55015
  --  37807   73771
  --  66601   11537
  --  32475   68436
  --  65861   35241
  --  65154   35982
  --  32341   11537
  --  43126   99893
  --  81648   91534
  --  93016   63953
  --  37226   43847
  --  24429   17917
  --  35226   99893
  --  95560   75176
  --  77626   32126
  --  16841   37678
  --  94072   18811
  --  49716   15715
  --  69498   94453
  --  77092   88716
  --  51658   41708
  --  99436   76299
  --  56787   27416
  --  53173   83774
  --  42871   37678
  --  39206   43847
  --  52384   37678
  --  19944   42936
  --  74914   19845
  --  65918   67721
  --  38226   56750
  --  86853   74909
  --  18560   15292"
