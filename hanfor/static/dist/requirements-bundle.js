!function(e){function t(t){for(var r,o,s=t[0],l=t[1],c=t[2],f=0,d=[];f<s.length;f++)o=s[f],i[o]&&d.push(i[o][0]),i[o]=0;for(r in l)Object.prototype.hasOwnProperty.call(l,r)&&(e[r]=l[r]);for(u&&u(t);d.length;)d.shift()();return a.push.apply(a,c||[]),n()}function n(){for(var e,t=0;t<a.length;t++){for(var n=a[t],r=!0,s=1;s<n.length;s++){var l=n[s];0!==i[l]&&(r=!1)}r&&(a.splice(t--,1),e=o(o.s=n[0]))}return e}var r={},i={4:0},a=[];function o(t){if(r[t])return r[t].exports;var n=r[t]={i:t,l:!1,exports:{}};return e[t].call(n.exports,n,n.exports,o),n.l=!0,n.exports}o.m=e,o.c=r,o.d=function(e,t,n){o.o(e,t)||Object.defineProperty(e,t,{enumerable:!0,get:n})},o.r=function(e){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},o.t=function(e,t){if(1&t&&(e=o(e)),8&t)return e;if(4&t&&"object"==typeof e&&e&&e.__esModule)return e;var n=Object.create(null);if(o.r(n),Object.defineProperty(n,"default",{enumerable:!0,value:e}),2&t&&"string"!=typeof e)for(var r in e)o.d(n,r,function(t){return e[t]}.bind(null,r));return n},o.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return o.d(t,"a",t),t},o.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)},o.p="";var s=window.webpackJsonp=window.webpackJsonp||[],l=s.push.bind(s);s.push=t,s=s.slice();for(var c=0;c<s.length;c++)t(s[c]);var u=l;a.push([221,0]),n()}({215:function(e,t){const n={":AND:":1,":OR:":1},r={":AND:":1,":OR:":1},i={},a={"(":1,")":1},o={":AND:":3,":OR:":2};class s{constructor(e){this.left=!1,this.value=e,this.right=!1,this.col_target=-1,this.update_target()}update_target(){const e=this.value.indexOf(":COL_INDEX_");if(e>=0){const t=parseInt(this.value.substring(e+11,e+13));t>=0&&(this.value=this.value.substring(e+14),this.col_target=t)}}evaluate(e,t){return function e(t,n,r){if(void 0===t)return!0;if(!1===t.left&&!1===t.right){let e="";if(-1!==t.col_target)e=n[t.col_target];else for(let t=0;t<r.length;t++)r[t]&&(e+=n[t]+" ");const i=t.value.indexOf(":NOT:");return i>=0?!l(t.value.substring(i+5),e):l(t.value,e)}let i=e(t.left,n,r);let a=e(t.right,n,r);if(":AND:"===t.value)return i&&a;if(":OR:"===t.value)return i||a}(this,e,t)}static is_search_string(e){return!(e in a||e in n)}static to_string(e){let t="";return!1!==e.left&&(t+=s.to_string(e.left)+" "),t+=e.value,!1!==e.right&&(t+=" "+s.to_string(e.right)),t}static peek(e){return e[e.length-1]}static searchArrayToTree(e){let t=[],a=[];for(let l=0,c=e.length;l<c;l++){const c=e[l];if(s.is_search_string(c))t.push(new s(c));else if(c in n){for(;a.length;){const e=s.peek(a);if(!(e in n&&(c in r&&o[c]<=o[e]||c in i&&o[c]<o[e])))break;{let e=t.pop(),n=t.pop(),r=new s(a.pop());r.left=n,r.right=e,t.push(r)}}a.push(c)}else if("("===c)a.push(c);else{if(")"!==c)throw"Error: Token unknown: "+c;{let e=!1;for(;a.length;){const n=a.pop();if("("===n){e=!0;break}{let e=t.pop(),r=t.pop(),i=new s(n);i.left=r,i.right=e,t.push(i)}}if(!e)throw"Error: parentheses mismatch."}}}for(;a.length;){const e=a.pop();if("("===e||")"===e)throw"Error: Parentheses mismatch.";let n=t.pop(),r=t.pop(),i=new s(e);i.left=r,i.right=n,t.push(i)}return 0===t.length&&t.push(new s("")),t[0]}static awesomeQuerySplitt0r(e,t){let r=e.split(/(:OR:|:AND:|\(|\))/g);if(r=r.filter(String),void 0!==t)for(let e=0,i=r.length;e<i;e++)r[e]in n||r[e]in a||(r[e]=":COL_INDEX_"+("00"+t).slice(-2)+":"+r[e]);return r}static fromQuery(e="",t){return s.searchArrayToTree(s.awesomeQuerySplitt0r(e,t))}}function l(e,t){return e=e.startsWith('""')&&e.endsWith('""')?"^\\s*"+e.substr(2,e.length-4)+"\\s*$":e.replace(/([^\\])?\"/g,"$1\\b"),new RegExp(e,"i").test(t)}e.exports={SearchNode:s}},216:function(e,t,n){var r,i,a;
/*!
 * jQuery UI Effects 1.12.1
 * http://jqueryui.com
 *
 * Copyright jQuery Foundation and other contributors
 * Released under the MIT license.
 * http://jquery.org/license
 */i=[n(3),n(5)],void 0===(a="function"==typeof(r=function(e){var t,n="ui-effects-animated",r=e;return e.effects={effect:{}},
/*!
 * jQuery Color Animations v2.1.2
 * https://github.com/jquery/jquery-color
 *
 * Copyright 2014 jQuery Foundation and other contributors
 * Released under the MIT license.
 * http://jquery.org/license
 *
 * Date: Wed Jan 16 08:47:09 2013 -0600
 */
function(e,t){var n,r=/^([\-+])=\s*(\d+\.?\d*)/,i=[{re:/rgba?\(\s*(\d{1,3})\s*,\s*(\d{1,3})\s*,\s*(\d{1,3})\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,parse:function(e){return[e[1],e[2],e[3],e[4]]}},{re:/rgba?\(\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,parse:function(e){return[2.55*e[1],2.55*e[2],2.55*e[3],e[4]]}},{re:/#([a-f0-9]{2})([a-f0-9]{2})([a-f0-9]{2})/,parse:function(e){return[parseInt(e[1],16),parseInt(e[2],16),parseInt(e[3],16)]}},{re:/#([a-f0-9])([a-f0-9])([a-f0-9])/,parse:function(e){return[parseInt(e[1]+e[1],16),parseInt(e[2]+e[2],16),parseInt(e[3]+e[3],16)]}},{re:/hsla?\(\s*(\d+(?:\.\d+)?)\s*,\s*(\d+(?:\.\d+)?)\%\s*,\s*(\d+(?:\.\d+)?)\%\s*(?:,\s*(\d?(?:\.\d+)?)\s*)?\)/,space:"hsla",parse:function(e){return[e[1],e[2]/100,e[3]/100,e[4]]}}],a=e.Color=function(t,n,r,i){return new e.Color.fn.parse(t,n,r,i)},o={rgba:{props:{red:{idx:0,type:"byte"},green:{idx:1,type:"byte"},blue:{idx:2,type:"byte"}}},hsla:{props:{hue:{idx:0,type:"degrees"},saturation:{idx:1,type:"percent"},lightness:{idx:2,type:"percent"}}}},s={byte:{floor:!0,max:255},percent:{max:1},degrees:{mod:360,floor:!0}},l=a.support={},c=e("<p>")[0],u=e.each;function f(e,t,n){var r=s[t.type]||{};return null==e?n||!t.def?null:t.def:(e=r.floor?~~e:parseFloat(e),isNaN(e)?t.def:r.mod?(e+r.mod)%r.mod:0>e?0:r.max<e?r.max:e)}function d(t){var r=a(),s=r._rgba=[];return t=t.toLowerCase(),u(i,function(e,n){var i,a=n.re.exec(t),l=a&&n.parse(a),c=n.space||"rgba";if(l)return i=r[c](l),r[o[c].cache]=i[o[c].cache],s=r._rgba=i._rgba,!1}),s.length?("0,0,0,0"===s.join()&&e.extend(s,n.transparent),r):n[t]}function p(e,t,n){return 6*(n=(n+1)%1)<1?e+(t-e)*n*6:2*n<1?t:3*n<2?e+(t-e)*(2/3-n)*6:e}c.style.cssText="background-color:rgba(1,1,1,.5)",l.rgba=c.style.backgroundColor.indexOf("rgba")>-1,u(o,function(e,t){t.cache="_"+e,t.props.alpha={idx:3,type:"percent",def:1}}),a.fn=e.extend(a.prototype,{parse:function(t,r,i,s){if(void 0===t)return this._rgba=[null,null,null,null],this;(t.jquery||t.nodeType)&&(t=e(t).css(r),r=void 0);var l=this,c=e.type(t),p=this._rgba=[];return void 0!==r&&(t=[t,r,i,s],c="array"),"string"===c?this.parse(d(t)||n._default):"array"===c?(u(o.rgba.props,function(e,n){p[n.idx]=f(t[n.idx],n)}),this):"object"===c?(u(o,t instanceof a?function(e,n){t[n.cache]&&(l[n.cache]=t[n.cache].slice())}:function(n,r){var i=r.cache;u(r.props,function(e,n){if(!l[i]&&r.to){if("alpha"===e||null==t[e])return;l[i]=r.to(l._rgba)}l[i][n.idx]=f(t[e],n,!0)}),l[i]&&e.inArray(null,l[i].slice(0,3))<0&&(l[i][3]=1,r.from&&(l._rgba=r.from(l[i])))}),this):void 0},is:function(e){var t=a(e),n=!0,r=this;return u(o,function(e,i){var a,o=t[i.cache];return o&&(a=r[i.cache]||i.to&&i.to(r._rgba)||[],u(i.props,function(e,t){if(null!=o[t.idx])return n=o[t.idx]===a[t.idx]})),n}),n},_space:function(){var e=[],t=this;return u(o,function(n,r){t[r.cache]&&e.push(n)}),e.pop()},transition:function(e,t){var n=a(e),r=n._space(),i=o[r],l=0===this.alpha()?a("transparent"):this,c=l[i.cache]||i.to(l._rgba),d=c.slice();return n=n[i.cache],u(i.props,function(e,r){var i=r.idx,a=c[i],o=n[i],l=s[r.type]||{};null!==o&&(null===a?d[i]=o:(l.mod&&(o-a>l.mod/2?a+=l.mod:a-o>l.mod/2&&(a-=l.mod)),d[i]=f((o-a)*t+a,r)))}),this[r](d)},blend:function(t){if(1===this._rgba[3])return this;var n=this._rgba.slice(),r=n.pop(),i=a(t)._rgba;return a(e.map(n,function(e,t){return(1-r)*i[t]+r*e}))},toRgbaString:function(){var t="rgba(",n=e.map(this._rgba,function(e,t){return null==e?t>2?1:0:e});return 1===n[3]&&(n.pop(),t="rgb("),t+n.join()+")"},toHslaString:function(){var t="hsla(",n=e.map(this.hsla(),function(e,t){return null==e&&(e=t>2?1:0),t&&t<3&&(e=Math.round(100*e)+"%"),e});return 1===n[3]&&(n.pop(),t="hsl("),t+n.join()+")"},toHexString:function(t){var n=this._rgba.slice(),r=n.pop();return t&&n.push(~~(255*r)),"#"+e.map(n,function(e){return 1===(e=(e||0).toString(16)).length?"0"+e:e}).join("")},toString:function(){return 0===this._rgba[3]?"transparent":this.toRgbaString()}}),a.fn.parse.prototype=a.fn,o.hsla.to=function(e){if(null==e[0]||null==e[1]||null==e[2])return[null,null,null,e[3]];var t,n,r=e[0]/255,i=e[1]/255,a=e[2]/255,o=e[3],s=Math.max(r,i,a),l=Math.min(r,i,a),c=s-l,u=s+l,f=.5*u;return t=l===s?0:r===s?60*(i-a)/c+360:i===s?60*(a-r)/c+120:60*(r-i)/c+240,n=0===c?0:f<=.5?c/u:c/(2-u),[Math.round(t)%360,n,f,null==o?1:o]},o.hsla.from=function(e){if(null==e[0]||null==e[1]||null==e[2])return[null,null,null,e[3]];var t=e[0]/360,n=e[1],r=e[2],i=e[3],a=r<=.5?r*(1+n):r+n-r*n,o=2*r-a;return[Math.round(255*p(o,a,t+1/3)),Math.round(255*p(o,a,t)),Math.round(255*p(o,a,t-1/3)),i]},u(o,function(t,n){var i=n.props,o=n.cache,s=n.to,l=n.from;a.fn[t]=function(t){if(s&&!this[o]&&(this[o]=s(this._rgba)),void 0===t)return this[o].slice();var n,r=e.type(t),c="array"===r||"object"===r?t:arguments,d=this[o].slice();return u(i,function(e,t){var n=c["object"===r?e:t.idx];null==n&&(n=d[t.idx]),d[t.idx]=f(n,t)}),l?((n=a(l(d)))[o]=d,n):a(d)},u(i,function(n,i){a.fn[n]||(a.fn[n]=function(a){var o,s=e.type(a),l="alpha"===n?this._hsla?"hsla":"rgba":t,c=this[l](),u=c[i.idx];return"undefined"===s?u:("function"===s&&(a=a.call(this,u),s=e.type(a)),null==a&&i.empty?this:("string"===s&&(o=r.exec(a))&&(a=u+parseFloat(o[2])*("+"===o[1]?1:-1)),c[i.idx]=a,this[l](c)))})})}),a.hook=function(t){var n=t.split(" ");u(n,function(t,n){e.cssHooks[n]={set:function(t,r){var i,o,s="";if("transparent"!==r&&("string"!==e.type(r)||(i=d(r)))){if(r=a(i||r),!l.rgba&&1!==r._rgba[3]){for(o="backgroundColor"===n?t.parentNode:t;(""===s||"transparent"===s)&&o&&o.style;)try{s=e.css(o,"backgroundColor"),o=o.parentNode}catch(e){}r=r.blend(s&&"transparent"!==s?s:"_default")}r=r.toRgbaString()}try{t.style[n]=r}catch(e){}}},e.fx.step[n]=function(t){t.colorInit||(t.start=a(t.elem,n),t.end=a(t.end),t.colorInit=!0),e.cssHooks[n].set(t.elem,t.start.transition(t.end,t.pos))}})},a.hook("backgroundColor borderBottomColor borderLeftColor borderRightColor borderTopColor color columnRuleColor outlineColor textDecorationColor textEmphasisColor"),e.cssHooks.borderColor={expand:function(e){var t={};return u(["Top","Right","Bottom","Left"],function(n,r){t["border"+r+"Color"]=e}),t}},n=e.Color.names={aqua:"#00ffff",black:"#000000",blue:"#0000ff",fuchsia:"#ff00ff",gray:"#808080",green:"#008000",lime:"#00ff00",maroon:"#800000",navy:"#000080",olive:"#808000",purple:"#800080",red:"#ff0000",silver:"#c0c0c0",teal:"#008080",white:"#ffffff",yellow:"#ffff00",transparent:[null,null,null,0],_default:"#ffffff"}}(r),function(){var t,n=["add","remove","toggle"],i={border:1,borderBottom:1,borderColor:1,borderLeft:1,borderRight:1,borderTop:1,borderWidth:1,margin:1,padding:1};function a(t){var n,r,i=t.ownerDocument.defaultView?t.ownerDocument.defaultView.getComputedStyle(t,null):t.currentStyle,a={};if(i&&i.length&&i[0]&&i[i[0]])for(r=i.length;r--;)"string"==typeof i[n=i[r]]&&(a[e.camelCase(n)]=i[n]);else for(n in i)"string"==typeof i[n]&&(a[n]=i[n]);return a}e.each(["borderLeftStyle","borderRightStyle","borderBottomStyle","borderTopStyle"],function(t,n){e.fx.step[n]=function(e){("none"!==e.end&&!e.setAttr||1===e.pos&&!e.setAttr)&&(r.style(e.elem,n,e.end),e.setAttr=!0)}}),e.fn.addBack||(e.fn.addBack=function(e){return this.add(null==e?this.prevObject:this.prevObject.filter(e))}),e.effects.animateClass=function(t,r,o,s){var l=e.speed(r,o,s);return this.queue(function(){var r,o=e(this),s=o.attr("class")||"",c=l.children?o.find("*").addBack():o;c=c.map(function(){return{el:e(this),start:a(this)}}),(r=function(){e.each(n,function(e,n){t[n]&&o[n+"Class"](t[n])})})(),c=c.map(function(){return this.end=a(this.el[0]),this.diff=function(t,n){var r,a,o={};for(r in n)a=n[r],t[r]!==a&&(i[r]||!e.fx.step[r]&&isNaN(parseFloat(a))||(o[r]=a));return o}(this.start,this.end),this}),o.attr("class",s),c=c.map(function(){var t=this,n=e.Deferred(),r=e.extend({},l,{queue:!1,complete:function(){n.resolve(t)}});return this.el.animate(this.diff,r),n.promise()}),e.when.apply(e,c.get()).done(function(){r(),e.each(arguments,function(){var t=this.el;e.each(this.diff,function(e){t.css(e,"")})}),l.complete.call(o[0])})})},e.fn.extend({addClass:(t=e.fn.addClass,function(n,r,i,a){return r?e.effects.animateClass.call(this,{add:n},r,i,a):t.apply(this,arguments)}),removeClass:function(t){return function(n,r,i,a){return arguments.length>1?e.effects.animateClass.call(this,{remove:n},r,i,a):t.apply(this,arguments)}}(e.fn.removeClass),toggleClass:function(t){return function(n,r,i,a,o){return"boolean"==typeof r||void 0===r?i?e.effects.animateClass.call(this,r?{add:n}:{remove:n},i,a,o):t.apply(this,arguments):e.effects.animateClass.call(this,{toggle:n},r,i,a)}}(e.fn.toggleClass),switchClass:function(t,n,r,i,a){return e.effects.animateClass.call(this,{add:n,remove:t},r,i,a)}})}(),function(){var t;function r(t,n,r,i){return e.isPlainObject(t)&&(n=t,t=t.effect),t={effect:t},null==n&&(n={}),e.isFunction(n)&&(i=n,r=null,n={}),("number"==typeof n||e.fx.speeds[n])&&(i=r,r=n,n={}),e.isFunction(r)&&(i=r,r=null),n&&e.extend(t,n),r=r||n.duration,t.duration=e.fx.off?0:"number"==typeof r?r:r in e.fx.speeds?e.fx.speeds[r]:e.fx.speeds._default,t.complete=i||n.complete,t}function i(t){return!(t&&"number"!=typeof t&&!e.fx.speeds[t])||"string"==typeof t&&!e.effects.effect[t]||!!e.isFunction(t)||"object"==typeof t&&!t.effect}function a(e,t){var n=t.outerWidth(),r=t.outerHeight(),i=/^rect\((-?\d*\.?\d*px|-?\d+%|auto),?\s*(-?\d*\.?\d*px|-?\d+%|auto),?\s*(-?\d*\.?\d*px|-?\d+%|auto),?\s*(-?\d*\.?\d*px|-?\d+%|auto)\)$/.exec(e)||["",0,n,r,0];return{top:parseFloat(i[1])||0,right:"auto"===i[2]?n:parseFloat(i[2]),bottom:"auto"===i[3]?r:parseFloat(i[3]),left:parseFloat(i[4])||0}}e.expr&&e.expr.filters&&e.expr.filters.animated&&(e.expr.filters.animated=(t=e.expr.filters.animated,function(r){return!!e(r).data(n)||t(r)})),!1!==e.uiBackCompat&&e.extend(e.effects,{save:function(e,t){for(var n=0,r=t.length;n<r;n++)null!==t[n]&&e.data("ui-effects-"+t[n],e[0].style[t[n]])},restore:function(e,t){for(var n,r=0,i=t.length;r<i;r++)null!==t[r]&&(n=e.data("ui-effects-"+t[r]),e.css(t[r],n))},setMode:function(e,t){return"toggle"===t&&(t=e.is(":hidden")?"show":"hide"),t},createWrapper:function(t){if(t.parent().is(".ui-effects-wrapper"))return t.parent();var n={width:t.outerWidth(!0),height:t.outerHeight(!0),float:t.css("float")},r=e("<div></div>").addClass("ui-effects-wrapper").css({fontSize:"100%",background:"transparent",border:"none",margin:0,padding:0}),i={width:t.width(),height:t.height()},a=document.activeElement;try{a.id}catch(e){a=document.body}return t.wrap(r),(t[0]===a||e.contains(t[0],a))&&e(a).trigger("focus"),r=t.parent(),"static"===t.css("position")?(r.css({position:"relative"}),t.css({position:"relative"})):(e.extend(n,{position:t.css("position"),zIndex:t.css("z-index")}),e.each(["top","left","bottom","right"],function(e,r){n[r]=t.css(r),isNaN(parseInt(n[r],10))&&(n[r]="auto")}),t.css({position:"relative",top:0,left:0,right:"auto",bottom:"auto"})),t.css(i),r.css(n).show()},removeWrapper:function(t){var n=document.activeElement;return t.parent().is(".ui-effects-wrapper")&&(t.parent().replaceWith(t),(t[0]===n||e.contains(t[0],n))&&e(n).trigger("focus")),t}}),e.extend(e.effects,{version:"1.12.1",define:function(t,n,r){return r||(r=n,n="effect"),e.effects.effect[t]=r,e.effects.effect[t].mode=n,r},scaledDimensions:function(e,t,n){if(0===t)return{height:0,width:0,outerHeight:0,outerWidth:0};var r="horizontal"!==n?(t||100)/100:1,i="vertical"!==n?(t||100)/100:1;return{height:e.height()*i,width:e.width()*r,outerHeight:e.outerHeight()*i,outerWidth:e.outerWidth()*r}},clipToBox:function(e){return{width:e.clip.right-e.clip.left,height:e.clip.bottom-e.clip.top,left:e.clip.left,top:e.clip.top}},unshift:function(e,t,n){var r=e.queue();t>1&&r.splice.apply(r,[1,0].concat(r.splice(t,n))),e.dequeue()},saveStyle:function(e){e.data("ui-effects-style",e[0].style.cssText)},restoreStyle:function(e){e[0].style.cssText=e.data("ui-effects-style")||"",e.removeData("ui-effects-style")},mode:function(e,t){var n=e.is(":hidden");return"toggle"===t&&(t=n?"show":"hide"),(n?"hide"===t:"show"===t)&&(t="none"),t},getBaseline:function(e,t){var n,r;switch(e[0]){case"top":n=0;break;case"middle":n=.5;break;case"bottom":n=1;break;default:n=e[0]/t.height}switch(e[1]){case"left":r=0;break;case"center":r=.5;break;case"right":r=1;break;default:r=e[1]/t.width}return{x:r,y:n}},createPlaceholder:function(t){var n,r=t.css("position"),i=t.position();return t.css({marginTop:t.css("marginTop"),marginBottom:t.css("marginBottom"),marginLeft:t.css("marginLeft"),marginRight:t.css("marginRight")}).outerWidth(t.outerWidth()).outerHeight(t.outerHeight()),/^(static|relative)/.test(r)&&(r="absolute",n=e("<"+t[0].nodeName+">").insertAfter(t).css({display:/^(inline|ruby)/.test(t.css("display"))?"inline-block":"block",visibility:"hidden",marginTop:t.css("marginTop"),marginBottom:t.css("marginBottom"),marginLeft:t.css("marginLeft"),marginRight:t.css("marginRight"),float:t.css("float")}).outerWidth(t.outerWidth()).outerHeight(t.outerHeight()).addClass("ui-effects-placeholder"),t.data("ui-effects-placeholder",n)),t.css({position:r,left:i.left,top:i.top}),n},removePlaceholder:function(e){var t="ui-effects-placeholder",n=e.data(t);n&&(n.remove(),e.removeData(t))},cleanUp:function(t){e.effects.restoreStyle(t),e.effects.removePlaceholder(t)},setTransition:function(t,n,r,i){return i=i||{},e.each(n,function(e,n){var a=t.cssUnit(n);a[0]>0&&(i[n]=a[0]*r+a[1])}),i}}),e.fn.extend({effect:function(){var t=r.apply(this,arguments),i=e.effects.effect[t.effect],a=i.mode,o=t.queue,s=o||"fx",l=t.complete,c=t.mode,u=[],f=function(t){var r=e(this),i=e.effects.mode(r,c)||a;r.data(n,!0),u.push(i),a&&("show"===i||i===a&&"hide"===i)&&r.show(),a&&"none"===i||e.effects.saveStyle(r),e.isFunction(t)&&t()};if(e.fx.off||!i)return c?this[c](t.duration,l):this.each(function(){l&&l.call(this)});function d(r){var o=e(this);function s(){e.isFunction(l)&&l.call(o[0]),e.isFunction(r)&&r()}t.mode=u.shift(),!1===e.uiBackCompat||a?"none"===t.mode?(o[c](),s()):i.call(o[0],t,function(){o.removeData(n),e.effects.cleanUp(o),"hide"===t.mode&&o.hide(),s()}):(o.is(":hidden")?"hide"===c:"show"===c)?(o[c](),s()):i.call(o[0],t,s)}return!1===o?this.each(f).each(d):this.queue(s,f).queue(s,d)},show:function(e){return function(t){if(i(t))return e.apply(this,arguments);var n=r.apply(this,arguments);return n.mode="show",this.effect.call(this,n)}}(e.fn.show),hide:function(e){return function(t){if(i(t))return e.apply(this,arguments);var n=r.apply(this,arguments);return n.mode="hide",this.effect.call(this,n)}}(e.fn.hide),toggle:function(e){return function(t){if(i(t)||"boolean"==typeof t)return e.apply(this,arguments);var n=r.apply(this,arguments);return n.mode="toggle",this.effect.call(this,n)}}(e.fn.toggle),cssUnit:function(t){var n=this.css(t),r=[];return e.each(["em","px","%","pt"],function(e,t){n.indexOf(t)>0&&(r=[parseFloat(n),t])}),r},cssClip:function(e){return e?this.css("clip","rect("+e.top+"px "+e.right+"px "+e.bottom+"px "+e.left+"px)"):a(this.css("clip"),this)},transfer:function(t,n){var r=e(this),i=e(t.to),a="fixed"===i.css("position"),o=e("body"),s=a?o.scrollTop():0,l=a?o.scrollLeft():0,c=i.offset(),u={top:c.top-s,left:c.left-l,height:i.innerHeight(),width:i.innerWidth()},f=r.offset(),d=e("<div class='ui-effects-transfer'></div>").appendTo("body").addClass(t.className).css({top:f.top-s,left:f.left-l,height:r.innerHeight(),width:r.innerWidth(),position:a?"fixed":"absolute"}).animate(u,t.duration,t.easing,function(){d.remove(),e.isFunction(n)&&n()})}}),e.fx.step.clip=function(t){t.clipInit||(t.start=e(t.elem).cssClip(),"string"==typeof t.end&&(t.end=a(t.end,t.elem)),t.clipInit=!0),e(t.elem).cssClip({top:t.pos*(t.end.top-t.start.top)+t.start.top,right:t.pos*(t.end.right-t.start.right)+t.start.right,bottom:t.pos*(t.end.bottom-t.start.bottom)+t.start.bottom,left:t.pos*(t.end.left-t.start.left)+t.start.left})}}(),t={},e.each(["Quad","Cubic","Quart","Quint","Expo"],function(e,n){t[n]=function(t){return Math.pow(t,e+2)}}),e.extend(t,{Sine:function(e){return 1-Math.cos(e*Math.PI/2)},Circ:function(e){return 1-Math.sqrt(1-e*e)},Elastic:function(e){return 0===e||1===e?e:-Math.pow(2,8*(e-1))*Math.sin((80*(e-1)-7.5)*Math.PI/15)},Back:function(e){return e*e*(3*e-2)},Bounce:function(e){for(var t,n=4;e<((t=Math.pow(2,--n))-1)/11;);return 1/Math.pow(4,3-n)-7.5625*Math.pow((3*t-2)/22-e,2)}}),e.each(t,function(t,n){e.easing["easeIn"+t]=n,e.easing["easeOut"+t]=function(e){return 1-n(1-e)},e.easing["easeInOut"+t]=function(e){return e<.5?n(2*e)/2:1-n(-2*e+2)/2}}),e.effects})?r.apply(t,i):r)||(e.exports=a)},217:function(e,t,n){var r,i,a;
/*!
 * jQuery UI Effects Highlight 1.12.1
 * http://jqueryui.com
 *
 * Copyright jQuery Foundation and other contributors
 * Released under the MIT license.
 * http://jquery.org/license
 */i=[n(3),n(5),n(216)],void 0===(a="function"==typeof(r=function(e){return e.effects.define("highlight","show",function(t,n){var r=e(this),i={backgroundColor:r.css("backgroundColor")};"hide"===t.mode&&(i.opacity=0),e.effects.saveStyle(r),r.css({backgroundImage:"none",backgroundColor:t.color||"#ffff99"}).animate(i,{queue:!1,duration:t.duration,easing:t.easing,complete:n})})})?r.apply(t,i):r)||(e.exports=a)},221:function(e,t,n){(function(e){n(19),n(12),n(18),n(17),n(152),n(16),n(217),n(15);const{SearchNode:t}=n(215);let r=n(156),{Textcomplete:i,Textarea:a}=n(155),o=new r([],{}),s=["","has_formalization"],l=["","Todo","Review","Done"],c=[""],u=[""],f=[!0,!0,!0,!0,!0,!0],d=[],p=JSON.parse(search_query),h={},g=[],m=sessionStorage.getItem("req_search_string"),v=sessionStorage.getItem("filter_status_string"),_=sessionStorage.getItem("filter_tag_string"),b=sessionStorage.getItem("filter_type_string"),y=void 0,w=void 0;function x(){m=e("#search_bar").val().trim(),sessionStorage.setItem("req_search_string",m),y=t.fromQuery(m)}function q(){function n(e,n,r){return n.length>0&&(e.length>0&&(e=e.concat([":AND:"])),e=e.concat(function(e){return["("].concat(e,[")"])}(t.awesomeQuerySplitt0r(n,r)))),e}d=[],v=e("#status-filter-input").val(),_=e("#tag-filter-input").val(),b=e("#type-filter-input").val(),sessionStorage.setItem("filter_status_string",v),sessionStorage.setItem("filter_tag_string",_),sessionStorage.setItem("filter_type_string",b),d=n(d=n(d=n(d,b,4),_,5),v,6),w=t.searchArrayToTree(d)}function C(e){let t=[];return e.rows({selected:!0}).every(function(){let e=this.data();t.push(e.id)}),t}function k(){e(".requirement_var_group").each(function(){e(this).hide(),e(this).removeClass("type-error")}),e(".formalization_card").each(function(t){const n=e(this).attr("title"),r=e("#requirement_scope"+n).val(),i=e("#requirement_pattern"+n).val();let a=e("#formalization_heading"+n),o=e("#requirement_var_group_p"+n),s=e("#requirement_var_group_q"+n),l=e("#requirement_var_group_r"+n),c=e("#requirement_var_group_s"+n),u=e("#requirement_var_group_t"+n),f=e("#requirement_var_group_u"+n);if(n in g)for(let t=0;t<g[n].length;t++)e("#formalization_var_"+g[n][t]+n).addClass("type-error"),a.addClass("type-error-head");else a.removeClass("type-error-head");switch(r){case"BEFORE":case"AFTER":o.show();break;case"BETWEEN":case"AFTER_UNTIL":o.show(),s.show()}switch(i){case"Absence":case"Universality":case"Existence":case"BoundedExistence":l.show();break;case"Invariant":case"Precedence":case"Response":case"MinDuration":case"MaxDuration":case"BoundedRecurrence":l.show(),c.show();break;case"PrecedenceChain1-2":case"PrecedenceChain2-1":case"ResponseChain1-2":case"ResponseChain2-1":case"BoundedResponse":case"BoundedInvariance":case"TimeConstrainedInvariant":l.show(),c.show(),u.show();break;case"ConstrainedChain":case"TimeConstrainedMinDuration":case"ConstrainedTimedExistence":l.show(),c.show(),u.show(),f.show();break;case"NotFormalizable":o.hide(),s.hide()}})}function O(){e(".formalization_card").each(function(t){const n=e(this).attr("title");let r="";const i=e("#requirement_scope"+n).find("option:selected").text().replace(/\s\s+/g," "),a=e("#requirement_pattern"+n).find("option:selected").text().replace(/\s\s+/g," ");"None"!==i&&"None"!==a&&(r=i+", "+a+".");let o=e("#formalization_var_p"+n).val(),s=e("#formalization_var_q"+n).val(),l=e("#formalization_var_r"+n).val(),c=e("#formalization_var_s"+n).val(),u=e("#formalization_var_t"+n).val(),f=e("#formalization_var_u"+n).val();o.length>0&&(r=r.replace(/{P}/g,o)),s.length>0&&(r=r.replace(/{Q}/g,s)),l.length>0&&(r=r.replace(/{R}/g,l)),c.length>0&&(r=r.replace(/{S}/g,c)),u.length>0&&(r=r.replace(/{T}/g,u)),f.length>0&&(r=r.replace(/{U}/g,f)),e("#current_formalization_textarea"+n).val(r)}),e("#requirement_formalization_updated").val("true")}function S(){e(".formalization_selector").change(function(){k(),O()}),e(".reqirement-variable, .req_var_type").change(function(){O()}),e(".delete_formalization").confirmation({rootSelector:".delete_formalization"}).click(function(){!function(t){let n=e(".modal-content");n.LoadingOverlay("show");const r=e("#requirement_id").val();e.post("api/req/del_formalization",{requirement_id:r,formalization_id:t},function(t){n.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):e("#formalization_accordion").html(t.html)}).done(function(){k(),O(),S(),T(),B()})}(e(this).attr("name"))})}function T(){e(".reqirement-variable").each(function(t){let n=new a(this),r=new i(n,{dropdown:{maxCount:10}});r.register([{match:/(^|\s|[!=&\|>]+)(\w+)$/,search:function(e,t){include_elems=function(e){return o.search(e)}(e),result=[];for(let e=0;e<Math.min(10,include_elems.length);e++)result.push(u[include_elems[e]]);t(result)},replace:function(e){return"$1"+e+" "}}]),e(this).on("blur click",function(e){r.dropdown.deactivate(),e.preventDefault()})})}function z(t){if(-1===t)return void alert("Requirement not found.");let n=e("#requirements_table").DataTable().row(t).data(),i=e(".modal-content");e("#requirement_modal").modal("show"),i.LoadingOverlay("show"),e("#formalization_accordion").html(""),e("#requirement_tag_field").data("bs.tokenfield").$input.autocomplete({source:s}),e.get("api/req/get",{id:n.id,row_idx:t},function(n){e("#requirement_id").val(n.id),e("#requirement_formalization_updated").val("false"),e("#modal_associated_row_index").val(t),u=n.available_vars,g=n.type_inference_errors,o=new r(u,{shouldSort:!0,threshold:.6,location:0,distance:100,maxPatternLength:12,minMatchCharLength:1,keys:void 0}),e("#requirement_modal_title").html(n.id+": "+n.type),e("#description_textarea").text(n.desc),e("#add_guess_description").text(n.desc),e("#formalization_accordion").html(n.formalizations_html),e("#requirement_scope").val(n.scope),e("#requirement_pattern").val(n.pattern),e("#requirement_tag_field").tokenfield("setTokens",n.tags),e("#requirement_status").val(n.status);let i=e("#csv_content_accordion");i.html(""),i.collapse("hide");let a=n.csv_data;for(const e in a)if(a.hasOwnProperty(e)){const t=a[e];i.append("<p><strong>"+e+":</strong>"+t+"</p>")}!1===n.success&&alert("Could Not load the Requirement: "+n.errormsg)}).done(function(){k(),T(),S(),e("#requirement_tag_field").on("tokenfield:createtoken",function(t){let n=e(this).tokenfield("getTokens");e.each(n,function(e,n){n.value===t.attrs.value&&t.preventDefault()})}),i.LoadingOverlay("hide",!0)})}function L(){let t=e("#requirements_table").DataTable(),n=[];e.each(t.columns().visible(),function(t,r){!1===r?(e("#col_toggle_button_"+t).removeClass("btn-info").addClass("btn-secondary"),n.push(!1)):(e("#col_toggle_button_"+t).removeClass("btn-secondary").addClass("btn-info"),n.push(!0))}),f=n}function N(t){t.columns().every(function(e){e>0&&t.column(e).header().append(" ("+e+")")}),e("#save_requirement_modal").click(function(){!function(t){let n=e(".modal-content");n.LoadingOverlay("show");const r=e("#requirement_id").val(),i=e("#requirement_tag_field").val(),a=e("#requirement_status").val(),o=e("#requirement_formalization_updated").val(),s=parseInt(e("#modal_associated_row_index").val());let l={};e(".formalization_card").each(function(t){let n={};n.id=e(this).attr("title"),e(this).find("select").each(function(){e(this).hasClass("scope_selector")&&(n.scope=e(this).val()),e(this).hasClass("pattern_selector")&&(n.pattern=e(this).val())}),n.expression_mapping={},e(this).find("textarea.reqirement-variable").each(function(){""!==e(this).attr("title")&&(n.expression_mapping[e(this).attr("title")]=e(this).val())}),l[n.id]=n}),e.post("api/req/update",{id:r,row_idx:s,update_formalization:o,tags:i,status:a,formalizations:JSON.stringify(l)},function(r){n.LoadingOverlay("hide",!0),!1===r.success?alert(r.errormsg):(t.row(s).data(r),e("#requirement_modal").modal("hide"))}).done(function(){B()})}(t)}),e("#search_bar").keypress(function(e){13===e.which&&(x(),t.draw())}),e("#type-filter-input").autocomplete({minLength:0,source:c,delay:100}),e("#status-filter-input").autocomplete({minLength:0,source:l,delay:100}),e("#tag-filter-input").autocomplete({minLength:0,source:s,delay:100}),e("#tag-filter-input, #status-filter-input, #type-filter-input").on("focus",function(){e(this).keydown()}).on("keypress",function(e){13===e.which&&(q(),t.draw())}),e("#table-filter-toggle").click(function(){e("#tag-filter-input").autocomplete({source:s}),e("#type-filter-input").autocomplete({source:c})}),e(".clear-all-filters").click(function(){e("#status-filter-input").val("").effect("highlight",{color:"green"},500),e("#tag-filter-input").val("").effect("highlight",{color:"green"},500),e("#type-filter-input").val("").effect("highlight",{color:"green"},500),e("#search_bar").val("").effect("highlight",{color:"green"},500),q(),x(),t.draw()}),e("#gen-req-from-selection").click(function(){let n=[];t.rows({search:"applied"}).every(function(){let e=this.data();n.push(e.id)}),e("#selected_requirement_ids").val(JSON.stringify(n)),e("#generate_req_form").submit()}),e("#gen-csv-from-selection").click(function(){let n=[];t.rows({search:"applied"}).every(function(){let e=this.data();n.push(e.id)}),e("#selected_csv_requirement_ids").val(JSON.stringify(n)),e("#generate_csv_form").submit()}),e(".colum-toggle-button").on("click",function(n){n.preventDefault();let r=t.column(e(this).attr("data-column"));r.visible(!r.visible()),L()}),e(".reset-colum-toggle").on("click",function(e){e.preventDefault(),t.columns(".default-col").visible(!0),t.columns(".extra-col").visible(!1),L()}),L(),e(".select-all-button").on("click",function(n){e(this).hasClass("btn-secondary")?t.rows({page:"current"}).select():t.rows({page:"current"}).deselect(),e(".select-all-button").toggleClass("btn-secondary btn-primary")}),t.on("user-select",function(){let t=e(".select-all-button");t.removeClass("btn-primary"),t.addClass("btn-secondary ")}),e("#multi-add-tag-input, #multi-remove-tag-input").autocomplete({minLength:0,source:s,delay:100}).on("focus",function(){e(this).keydown()}).val(""),e("#multi-set-status-input").autocomplete({minLength:0,source:l,delay:100}).on("focus",function(){e(this).keydown()}).val(""),e(".apply-multi-edit").click(function(){!function(t){let n=e("body");n.LoadingOverlay("show");let r=e("#multi-add-tag-input").val().trim(),i=e("#multi-remove-tag-input").val().trim(),a=e("#multi-set-status-input").val().trim(),o=C(t);e.post("api/req/multi_update",{add_tag:r,remove_tag:i,set_status:a,selected_ids:JSON.stringify(o)},function(e){n.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):location.reload()})}(t)}),e(".add_top_guess_button").confirmation({rootSelector:".add_top_guess_button"}).click(function(){!function(t){let n=e("body");n.LoadingOverlay("show");let r=C(t),i=e("#top_guess_append_mode").val();e.post("api/req/multi_add_top_guess",{selected_ids:JSON.stringify(r),insert_mode:i},function(e){n.LoadingOverlay("hide",!0),!1===e.success?alert(e.errormsg):location.reload()})}(t)})}function I(t){let n=e("#requirements_table").DataTable({language:{emptyTable:"Loading data."},paging:!0,stateSave:!0,select:{style:"os",selector:"td:first-child"},pageLength:50,lengthMenu:[[10,50,100,500,-1],[10,50,100,500,"All"]],dom:'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',ajax:"api/req/gets",deferRender:!0,columnDefs:t,createdRow:function(t,n,r){"Heading"===n.type&&e(t).addClass("bg-primary"),"Information"===n.type&&e(t).addClass("table-info"),"Requirement"===n.type&&e(t).addClass("table-warning"),"not set"===n.type&&e(t).addClass("table-light")},initComplete:function(){e("#search_bar").val(m),e("#type-filter-input").val(b),e("#tag-filter-input").val(_),e("#status-filter-input").val(v),function(t){e("#requirements_table").find("tbody").on("click","a",function(n){n.preventDefault(),z(t.row(e(n.target).parent()).index())})}(n),N(n),function(t){if(t.q.length>0){e("#status-filter-input").val(""),e("#tag-filter-input").val(""),e("#type-filter-input").val("");const n=":COL_INDEX_"+function(e){let t="00"+e;return t.substr(t.length-2)}(t.col).toString()+":"+t.q;e("#search_bar").val(n)}}(p),x(),q(),e.fn.dataTable.ext.search.push(function(e,t,n){return function(e){return y.evaluate(e,f)&&w.evaluate(e,f)}(t)}),this.api().draw()}})}function R(){let t=e("#requirement_guess_modal"),n=e("#available_guesses_cards"),r=e(".modal-content"),i=e("#requirement_id").val();function a(e){let t='<div id="available_guesses_cards" >                <div class="card">                    <div class="pl-1 pr-1">                        <p>'+e.string+'                        </p>                    </div>                    <button type="button" class="btn btn-success btn-sm add_guess"                            title="Add formalization"                            data-scope="'+e.scope+'"                            data-pattern="'+e.pattern+"\"                            data-mapping='"+JSON.stringify(e.mapping)+"'>                        <strong>+ Add this formalization +</strong>                    </button>                </div>            </div>";n.append(t)}t.modal("show"),r.LoadingOverlay("show"),n.html(""),e.post("api/req/get_available_guesses",{requirement_id:i},function(e){if(!1===e.success)alert(e.errormsg);else for(let t=0;t<e.available_guesses.length;t++)a(e.available_guesses[t])}).done(function(){e(".add_guess").click(function(){!function(t,n,r){let i=e(".modal-content");i.LoadingOverlay("show");let a=e("#requirement_id").val();e.post("api/req/add_formalization_from_guess",{requirement_id:a,scope:t,pattern:n,mapping:JSON.stringify(r)},function(t){i.LoadingOverlay("hide",!0),!1===t.success?alert(t.errormsg):e("#formalization_accordion").append(t.html)}).done(function(){k(),O(),S(),T(),B()})}(e(this).data("scope"),e(this).data("pattern"),e(this).data("mapping"))}),r.LoadingOverlay("hide",!0)})}function D(){let t=[{orderable:!1,className:"select-checkbox",targets:[0],data:null,defaultContent:""},{targets:[1],data:"pos"},{targets:[2],data:"id",render:function(e,t,n,r){return result='<a href="#">'+e+"</a>",result}},{targets:[3],data:"desc"},{targets:[4],data:"type",render:function(e,t,n,r){return c.indexOf(e)<=-1&&c.push(e),e}},{targets:[5],data:"tags",render:function(t,n,r,i){return result="",e(t).each(function(e,t){var n;t.length>0&&(result+='<span class="badge" style="background-color: '+(n=t,h.hasOwnProperty(n)?h[n]:"#5bc0de")+'">'+t+"</span></br>",s.indexOf(t)<=-1&&s.push(t))}),r.formal.length>0&&(result+='<span class="badge badge-success">has_formalization</span></br>'),result}},{targets:[6],data:"status",render:function(e,t,n,r){return result='<span class="badge badge-info">'+e+"</span></br>",result}},{targets:[7],data:"formal",render:function(t,n,r,i){return result="",r.formal.length>0&&e(t).each(function(e,t){t.length>0&&(result+="<p>"+t+"</p>")}),result}}];e.get("api/table/colum_defs","",function(e){const n=e.col_defs.length;for(let r=0;r<n;r++)t.push({targets:[parseInt(e.col_defs[r].target)],data:e.col_defs[r].csv_name,visible:!1,searchable:!0})}).done(function(){I(t)})}function M(){e("#requirement_tag_field").tokenfield({autocomplete:{source:s,delay:100},showAutocompleteOnFocus:!0}),e("#requirement_modal").on("hidden.bs.modal",function(t){e("#requirement_tag_field").val(""),e("#requirement_tag_field-tokenfield").val("")}),e("#add_formalization").click(function(){!function(){let t=e(".modal-content");t.LoadingOverlay("show");const n=e("#requirement_id").val();e.post("api/req/new_formalization",{id:n},function(n){t.LoadingOverlay("hide",!0),!1===n.success?alert(n.errormsg):e("#formalization_accordion").append(n.html)}).done(function(){k(),O(),S(),T(),B()})}()}),e("#add_gussed_formalization").click(function(){R()}),e(".modal").on("hidden.bs.modal",function(t){e(".modal:visible").length&&e("body").addClass("modal-open")}),k()}function B(){e.get("api/logs/get","",function(t){e("#log_textarea").html(t)}).done(function(){e(".req_direct_link").click(function(){z(function(t){let n=-1;return e("#requirements_table").DataTable().column(2).data().filter(function(e,r){return e===t&&(n=r,!0)}),n}(e(this).data("rid")))}),e("#log_textarea").scrollTop(1e5)})}e(document).ready(function(){e.get("api/meta/get","",function(e){h=e.tag_colors}),D(),M(),B()})}).call(this,n(3))}});