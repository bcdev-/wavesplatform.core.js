(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('apiService', ['Restangular', function (rest) {
            var blocksApi = rest.all('blocks');

            this.blocks = {
                height: function() {
                    return blocksApi.get('height');
                },
                last: function() {
                    return blocksApi.get('last');
                },
                list: function (startHeight, endHeight) {
                    return blocksApi.one('seq', startHeight).all(endHeight).getList();
                }
            };

            var addressApi = rest.all('addresses');
            this.address = {
                balance: function (address) {
                    return addressApi.one('balance', address).get();
                }
            };

            var transactionApi = rest.all('transactions');
            this.transactions = {
                unconfirmed: function () {
                    return transactionApi.all('unconfirmed').getList();
                },
                list: function (address, max) {
                    max = max || 50;
                    return transactionApi.one('address', address).one('limit', max).getList();
                },
                info: function (transactionId) {
                    return transactionApi.one('info', transactionId).get();
                }
            };

            var wavesApi = rest.all('waves');
            this.broadcastPayment = function (signedPaymentTransaction) {
                return wavesApi.all('broadcast-signed-payment').post(signedPaymentTransaction);
            };

            var assetApi = rest.all('assets');
            var assetBroadcastApi = assetApi.all('broadcast');
            this.assets = {
                balance: function (address, assetId) {
                    var rest = assetApi.one('balance', address);
                    if (angular.isDefined(assetId))
                        rest = rest.all(assetId);

                    return rest.get();
                },
                issue: function (signedAssetIssueTransaction) {
                    return assetBroadcastApi.all('issue').post(signedAssetIssueTransaction);
                },
                reissue: function (signedAssetReissueTransaction) {
                    return assetBroadcastApi.all('reissue').post(signedAssetReissueTransaction);
                },
                transfer: function (signedAssetTransferTransaction) {
                    return assetBroadcastApi.all('transfer').post(signedAssetTransferTransaction);
                }
            };
            
            {
                var currenciesToUpdate = [Currency.BTC, Currency.CNY, Currency.EUR, Currency.USD];
				for (var i = 0, len = currenciesToUpdate.length; i < len; i++) {
				  var currency = currenciesToUpdate[i];
                    if (currency.id !== undefined) {
                        var self = this;
                        this.transactions.info(currency.id).then(function (response) {
                            var id = response.assetId;
                            var description = JSON.parse(response.description);
                            console.log(id);
                            console.log(description);
                            var currenciesToUpdate2 = [Currency.BTC, Currency.CNY, Currency.EUR, Currency.USD];
                            for (var i = 0, len = currenciesToUpdate.length; i < len; i++) {
                                var currency = currenciesToUpdate[i];
                                if (currency.id == id) {
                                    currency.gatewayCommunicationKey = Base58.decode(description.gatewayCommunicationKey);
                                    currency.gatewayURL = description.gatewayURL;
                                    currency.displayName = description.displayName;
                                    currency.symbol = description.symbol;
                                    currency.precision = response.decimals;
                                }
                            }
                        });
//                        var a = this.transactions.info(currency.id);
//                        console.log(a);
                    }
				}
            }
        }]);
})();
