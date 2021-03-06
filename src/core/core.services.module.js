(function() {
    'use strict';

    var DEFAULT_TESTNET_NODE_ADDRESS = 'http://52.30.47.67:6869';

    angular.module('waves.core.services', ['waves.core', 'restangular'])
        .config(function () {
            if (!String.prototype.startsWith) {
                Object.defineProperty(String.prototype, 'startsWith', {
                    enumerable: false,
                    configurable: false,
                    writable: false,
                    value: function(searchString, position) {
                        position = position || 0;
                        return this.lastIndexOf(searchString, position) === position;
                    }
                });
            }
        })
        .run(['Restangular', function(rest) {
            rest.setBaseUrl(DEFAULT_TESTNET_NODE_ADDRESS);
        }]);
})();
